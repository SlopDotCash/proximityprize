#!/usr/bin/env python3
"""Exact MILP companion for the source-seven no-eight signature search.

This encodes the same predicates as
``probe_rate_quarter_noeight_source7_signatures_z3.py`` using binary linear
variables and HiGHS through ``scipy.optimize.milp``.  The two independent
backends make SAT certificates easy to cross-check and give a second route
to exhaustive UNSAT.
"""

from argparse import ArgumentParser
from itertools import combinations
from math import inf

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array

from probe_rate_quarter_noeight_source7_signatures_z3 import report, verify


SOURCE_SIZE = 7
COMPLEMENT_SIZE = 9


class BinaryMILP:
    def __init__(self):
        self.names = []
        self.rows = []

    def variable(self, name):
        index = len(self.names)
        self.names.append(name)
        return index

    def constraint(self, coefficients, lower=-inf, upper=inf):
        self.rows.append((coefficients, lower, upper))

    def equal(self, coefficients, value):
        self.constraint(coefficients, value, value)

    def matrix(self):
        row_index = []
        column_index = []
        values = []
        lower = []
        upper = []
        for r, (coefficients, lo, hi) in enumerate(self.rows):
            for variable, coefficient in coefficients.items():
                if coefficient:
                    row_index.append(r)
                    column_index.append(variable)
                    values.append(coefficient)
            lower.append(lo)
            upper.append(hi)
        matrix = coo_array(
            (np.asarray(values, dtype=float),
             (np.asarray(row_index), np.asarray(column_index))),
            shape=(len(self.rows), len(self.names))).tocsr()
        return LinearConstraint(matrix, np.asarray(lower), np.asarray(upper))


def add_and(model, inputs, name):
    output = model.variable(name)
    for variable in inputs:
        model.constraint({output: 1, variable: -1}, upper=0)
    coefficients = {output: 1}
    for variable in inputs:
        coefficients[variable] = coefficients.get(variable, 0) - 1
    model.constraint(coefficients, lower=1 - len(inputs))
    return output


def add_fresh_and(model, missed_inputs, name):
    """Output is the conjunction of the negations of missed_inputs."""
    output = model.variable(name)
    for variable in missed_inputs:
        model.constraint({output: 1, variable: 1}, upper=1)
    coefficients = {output: 1}
    for variable in missed_inputs:
        coefficients[variable] = coefficients.get(variable, 0) + 1
    model.constraint(coefficients, lower=1)
    return output


def add_cardinality(coefficients, variables, coefficient=1):
    for variable in variables:
        coefficients[variable] = coefficients.get(variable, 0) + coefficient


def build_model(signatures=13, max_balanced_witnesses=2,
                regular_only=False, regular_balance_only=False):
    model = BinaryMILP()
    root = [[model.variable(f"root_{s}_{i}") for i in range(SOURCE_SIZE)]
            for s in range(signatures)]
    missed = [[model.variable(f"missed_{s}_{i}")
               for i in range(COMPLEMENT_SIZE)]
              for s in range(signatures)]
    regular = [model.variable(f"regular_{s}") for s in range(signatures)]

    for s in range(signatures):
        root_card = {}
        add_cardinality(root_card, root[s])
        model.constraint(root_card, upper=3)
        missed_le_root = dict(root_card)
        add_cardinality(missed_le_root, missed[s], coefficient=-1)
        model.constraint(missed_le_root, lower=0)

        # E-cardinality is at most three.  These two inequalities make the
        # indicator exact: regular_s iff |E_s|=3 (then |T_s|=3 follows).
        ecard_minus_regular = {regular[s]: -3}
        add_cardinality(ecard_minus_regular, missed[s])
        model.constraint(ecard_minus_regular, lower=0)
        ecard_upper = {regular[s]: -1}
        add_cardinality(ecard_upper, missed[s])
        model.constraint(ecard_upper, upper=2)
        if regular_only:
            model.equal(root_card, 3)
            ecard = {}
            add_cardinality(ecard, missed[s])
            model.equal(ecard, 3)

    # Canonicalize the first signature under independent coordinate
    # permutations.  Order all remaining labels by their binary code.
    for i in range(SOURCE_SIZE - 1):
        model.constraint({root[0][i + 1]: 1, root[0][i]: -1}, upper=0)
    for i in range(COMPLEMENT_SIZE - 1):
        model.constraint({missed[0][i + 1]: 1, missed[0][i]: -1}, upper=0)
    weights = [1 << i for i in range(SOURCE_SIZE + COMPLEMENT_SIZE)]
    for s in range(1, signatures - 1):
        ordering = {}
        for weight, left, right in zip(
                weights, root[s] + missed[s], root[s + 1] + missed[s + 1]):
            ordering[left] = ordering.get(left, 0) + weight
            ordering[right] = ordering.get(right, 0) - weight
        model.constraint(ordering, upper=-1)

    pair_common = {}
    for a, b in combinations(range(signatures), 2):
        common = [add_and(model, [root[a][i], root[b][i]],
                          f"pair_root_{a}_{b}_{i}")
                  for i in range(SOURCE_SIZE)]
        common += [add_fresh_and(model, [missed[a][i], missed[b][i]],
                                 f"pair_fresh_{a}_{b}_{i}")
                   for i in range(COMPLEMENT_SIZE)]
        pair_common[(a, b)] = common
        pair_card = {}
        add_cardinality(pair_card, common)
        model.constraint(pair_card, upper=7)

    # At most three regular signatures share a root triple.  When all four
    # members are regular, equality of their size-three roots would make the
    # three displayed pair intersections sum to nine, so cap it by eight.
    for a, b, c, d in combinations(range(signatures), 4):
        fiber = {}
        add_cardinality(fiber, pair_common[(a, b)][:SOURCE_SIZE])
        add_cardinality(fiber, pair_common[(a, c)][:SOURCE_SIZE])
        add_cardinality(fiber, pair_common[(a, d)][:SOURCE_SIZE])
        add_cardinality(fiber, [regular[a], regular[b], regular[c], regular[d]])
        model.constraint(fiber, upper=12)

    balance = {}
    for a, b, c in combinations(range(signatures), 3):
        common = [add_and(model, [root[a][i], root[b][i], root[c][i]],
                          f"triple_root_{a}_{b}_{c}_{i}")
                  for i in range(SOURCE_SIZE)]
        common += [add_fresh_and(
            model, [missed[a][i], missed[b][i], missed[c][i]],
            f"triple_fresh_{a}_{b}_{c}_{i}")
            for i in range(COMPLEMENT_SIZE)]
        flag = model.variable(f"balance_{a}_{b}_{c}")
        balance[(a, b, c)] = flag
        threshold = {flag: -4}
        add_cardinality(threshold, common)
        model.constraint(threshold, lower=0, upper=3)

    for a, b in combinations(range(signatures), 2):
        witnesses = {}
        for c in range(signatures):
            if c not in (a, b):
                triple = tuple(sorted((a, b, c)))
                witness = balance[triple]
                if regular_balance_only:
                    witness = add_and(
                        model, [witness, regular[a], regular[b], regular[c]],
                        f"regular_balance_{a}_{b}_{c}")
                witnesses[witness] = 1
        model.constraint(witnesses, upper=max_balanced_witnesses)

    return model, root, missed


def selected(solution, row):
    return tuple(i for i, variable in enumerate(row)
                 if solution[variable] > 0.5)


def run(signatures=13, maximum=2, regular_only=False, timeout=300,
        regular_balance_only=False):
    model, root, missed = build_model(
        signatures, maximum, regular_only, regular_balance_only)
    print({"variables": len(model.names), "constraints": len(model.rows)},
          flush=True)
    result = milp(
        c=np.zeros(len(model.names)),
        integrality=np.ones(len(model.names)),
        bounds=Bounds(np.zeros(len(model.names)), np.ones(len(model.names))),
        constraints=model.matrix(),
        options={"time_limit": timeout, "presolve": True, "mip_rel_gap": 0.0},
    )
    print({"status": result.status, "message": result.message,
           "signatures": signatures, "maximum": maximum,
           "regular_only": regular_only,
           "regular_balance_only": regular_balance_only}, flush=True)
    if result.x is None:
        return result.status
    rows = [(selected(result.x, root[s]), selected(result.x, missed[s]))
            for s in range(signatures)]
    verify(rows, maximum, regular_balance_only)
    report(rows)
    return result.status


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--signatures", type=int, default=13)
    parser.add_argument("--max-balanced-witnesses", type=int, default=2)
    parser.add_argument("--regular-only", action="store_true")
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--regular-balance-only", action="store_true")
    args = parser.parse_args()
    status = run(args.signatures, args.max_balanced_witnesses,
                 args.regular_only, args.timeout, args.regular_balance_only)
    raise SystemExit(0 if status == 0 else 1)
