#!/usr/bin/env python3
"""Exact Z3 search for source-seven no-eight outsider signatures.

Each outsider is represented by a source-root set ``T subset Fin 7`` and a
missed set ``E subset Fin 9``.  The model enforces the constraints currently
available from the Lean reduction:

* ``|E| <= |T| <= 3``;
* ``2 + |T_i intersect T_j| <= |E_i union E_j|`` for every pair;
* at most three regular signatures (``|T|=|E|=3``) in each fixed root fiber;
* the exact ternary balance predicate

    ``4 + |E_i union E_j union E_k| <=
       9 + |T_i intersect T_j intersect T_k|``.

The balance predicate is not forbidden: in the polynomial model it forces
the third point onto the secant through the first two.  The default query
asks whether thirteen signatures can avoid a pair with three other balanced
witnesses.  UNSAT would force five points onto one secant and close the
source-seven residual by the relevant-line packing bound.  SAT produces a
finite signature countermodel only; it does not assert polynomial
realizability.
"""

from argparse import ArgumentParser
from itertools import combinations
import math
import random

from z3 import (And, Bool, If, Implies, Not, Or, PbEq, PbLe, Solver,
                SolverFor, is_true, sat)


SOURCE_SIZE = 7
COMPLEMENT_SIZE = 9


def bool_sum(bits):
    return sum(If(bit, 1, 0) for bit in bits)


def lex_less(left, right):
    """Unsigned binary-code order, expressed without integer arithmetic."""
    clauses = []
    for i in reversed(range(len(left))):
        higher_equal = [left[j] == right[j]
                        for j in range(i + 1, len(left))]
        clauses.append(And(*higher_equal, Not(left[i]), right[i]))
    return Or(*clauses)


def build_solver(signatures=13, max_balanced_witnesses=2, timeout_ms=0,
                 regular_only=False, second_intersections=None,
                 engine="qffd", regular_balance_only=False,
                 pb_solver="solver", threads=1, regular_count=None,
                 first_regular=False):
    solver = SolverFor("QF_FD") if engine == "qffd" else Solver()
    if timeout_ms:
        solver.set(timeout=timeout_ms)
    if engine == "qffd":
        solver.set("pb.solver", pb_solver)
        solver.set(threads=threads)

    root = [[Bool(f"root_{s}_{i}") for i in range(SOURCE_SIZE)]
            for s in range(signatures)]
    missed = [[Bool(f"missed_{s}_{i}") for i in range(COMPLEMENT_SIZE)]
              for s in range(signatures)]
    for s in range(signatures):
        # |E| <= |T| is |E| + |source \ T| <= 7.
        solver.add(PbLe([(bit, 1) for bit in missed[s]] +
                        [(Not(bit), 1) for bit in root[s]], SOURCE_SIZE))
        solver.add(PbLe([(bit, 1) for bit in root[s]], 3))
        if regular_only:
            solver.add(PbEq([(bit, 1) for bit in root[s]], 3))
            solver.add(PbEq([(bit, 1) for bit in missed[s]], 3))

    # Coordinate symmetry: the first root and missed sets are initial
    # segments.  Independent source/complement permutations make this WLOG.
    for i in range(SOURCE_SIZE - 1):
        solver.add(Implies(root[0][i + 1], root[0][i]))
    for i in range(COMPLEMENT_SIZE - 1):
        solver.add(Implies(missed[0][i + 1], missed[0][i]))

    # Signature labels beyond the canonical first member are immaterial.
    # Strict binary-code ordering removes their factorial symmetry; the pair
    # law itself rules out duplicate signatures.
    signature_bits = [root[s] + missed[s] for s in range(signatures)]
    order_start = 1

    if second_intersections is not None:
        root_intersection, missed_intersection = second_intersections
        if not (0 <= root_intersection <= 3 and
                0 <= missed_intersection <= 3 and
                root_intersection + missed_intersection <= 4):
            raise ValueError("invalid pair intersection sizes")
        # The first member is {0,1,2} on both sides.  Its stabilizer makes the
        # displayed second member canonical for the chosen intersection sizes.
        for i in range(SOURCE_SIZE):
            value = (i < root_intersection or
                     3 <= i < 3 + (3 - root_intersection))
            solver.add(root[1][i] == value)
        for i in range(COMPLEMENT_SIZE):
            value = (i < missed_intersection or
                     3 <= i < 3 + (3 - missed_intersection))
            solver.add(missed[1][i] == value)
        order_start = 2

    # The all-outsider global-core pair law.
    for s, t in combinations(range(signatures), 2):
        # Since |E_s union E_t| = 9 - |complement E_s intersect
        # complement E_t|, the pair law is the positive PB constraint below.
        terms = [(And(root[s][i], root[t][i]), 1)
                 for i in range(SOURCE_SIZE)]
        terms += [(And(Not(missed[s][i]), Not(missed[t][i])), 1)
                  for i in range(COMPLEMENT_SIZE)]
        solver.add(PbLe(terms, 7))

    regular = [And(PbEq([(bit, 1) for bit in root[s]], 3),
                   PbEq([(bit, 1) for bit in missed[s]], 3))
               for s in range(signatures)]
    if first_regular:
        solver.add(regular[0])
    if regular_count is not None:
        solver.add(PbEq([(flag, 1) for flag in regular], regular_count))

    # Type and label symmetry: regular rows form an initial segment, and
    # codes increase strictly within either type.  The canonical first (and
    # optional second) rows are excluded from code ordering.
    for s in range(signatures - 1):
        solver.add(Implies(regular[s + 1], regular[s]))
        if s >= order_start:
            solver.add(Implies(regular[s] == regular[s + 1],
                               lex_less(signature_bits[s],
                                        signature_bits[s + 1])))

    # The landed fixed-regular-root-fiber cap is three.
    for quad in combinations(range(signatures), 4):
        same_root = []
        first = quad[0]
        for s in quad[1:]:
            same_root.extend(root[first][i] == root[s][i]
                             for i in range(SOURCE_SIZE))
        solver.add(Not(And(*(regular[s] for s in quad), *same_root)))

    balance = {}
    for triple in combinations(range(signatures), 3):
        a, b, c = triple
        # Balance is |E union| + |source \ (T common)| <= 12.
        terms = [(Or(missed[a][i], missed[b][i], missed[c][i]), 1)
                 for i in range(COMPLEMENT_SIZE)]
        terms += [(Not(And(root[a][i], root[b][i], root[c][i])), 1)
                  for i in range(SOURCE_SIZE)]
        balance[triple] = PbLe(terms, 12)

    # A balanced triple containing pair {a,b} puts its third point on the
    # secant through a,b.  Bound the number of other points forced there.
    for a, b in combinations(range(signatures), 2):
        witnesses = []
        for c in range(signatures):
            if c == a or c == b:
                continue
            witness = balance[tuple(sorted((a, b, c)))]
            if regular_balance_only:
                witness = And(witness, regular[a], regular[b], regular[c])
            witnesses.append(witness)
        solver.add(PbLe([(witness, 1) for witness in witnesses],
                        max_balanced_witnesses))

    return solver, root, missed, balance


def selected(model, row):
    return tuple(i for i, bit in enumerate(row)
                 if is_true(model.eval(bit, model_completion=True)))


def balanced(row_a, row_b, row_c):
    roots = set(row_a[0]) & set(row_b[0]) & set(row_c[0])
    misses = set(row_a[1]) | set(row_b[1]) | set(row_c[1])
    return 4 + len(misses) <= 9 + len(roots)


def verify(rows, max_balanced_witnesses, regular_balance_only=False):
    assert all(len(e) <= len(t) <= 3 for t, e in rows)
    assert all(2 + len(set(rows[a][0]) & set(rows[b][0])) <=
               len(set(rows[a][1]) | set(rows[b][1]))
               for a, b in combinations(range(len(rows)), 2))
    for root in {row[0] for row in rows}:
        regular_count = sum(t == root and len(t) == len(e) == 3
                            for t, e in rows)
        assert regular_count <= 3
    for a, b in combinations(range(len(rows)), 2):
        witness_count = sum(
            balanced(rows[a], rows[b], rows[c]) and
            (not regular_balance_only or
             all(len(rows[s][0]) == len(rows[s][1]) == 3
                 for s in (a, b, c)))
            for c in range(len(rows)) if c not in (a, b)
        )
        assert witness_count <= max_balanced_witnesses


def report(rows):
    pair_witnesses = {}
    for a, b in combinations(range(len(rows)), 2):
        witnesses = tuple(
            c for c in range(len(rows))
            if c not in (a, b) and balanced(rows[a], rows[b], rows[c])
        )
        pair_witnesses[(a, b)] = witnesses
    triples = [triple for triple in combinations(range(len(rows)), 3)
               if balanced(*(rows[i] for i in triple))]
    histogram = {}
    for row in rows:
        key = (len(row[0]), len(row[1]))
        histogram[key] = histogram.get(key, 0) + 1
    max_count = max(map(len, pair_witnesses.values()), default=0)
    print({
        "cardinality_histogram": histogram,
        "balanced_triples": len(triples),
        "max_balanced_witnesses_on_pair": max_count,
        "rich_pairs": {pair: ws for pair, ws in pair_witnesses.items()
                       if len(ws) == max_count},
    })
    for index, (root, missed) in enumerate(rows):
        print({"signature": index, "root": root, "missed": missed})


def regular_catalogue():
    roots = [sum(1 << i for i in block)
             for block in combinations(range(SOURCE_SIZE), 3)]
    misses = [sum(1 << i for i in block)
              for block in combinations(range(COMPLEMENT_SIZE), 3)]
    return [(root, missed) for root in roots for missed in misses]


def compatible(left, right):
    return (2 + (left[0] & right[0]).bit_count() <=
            (left[1] | right[1]).bit_count())


def mask_balanced(a, b, c):
    return (4 + (a[1] | b[1] | c[1]).bit_count() <=
            9 + (a[0] & b[0] & c[0]).bit_count())


def witness_excess(rows, maximum):
    counts = [[0] * len(rows) for _ in rows]
    for a, b, c in combinations(range(len(rows)), 3):
        if mask_balanced(rows[a], rows[b], rows[c]):
            counts[a][b] += 1
            counts[b][a] += 1
            counts[a][c] += 1
            counts[c][a] += 1
            counts[b][c] += 1
            counts[c][b] += 1
    return sum(max(0, counts[a][b] - maximum) ** 2
               for a in range(len(rows)) for b in range(a + 1, len(rows)))


def tuple_from_masks(row):
    root, missed = row
    return (tuple(i for i in range(SOURCE_SIZE) if root & (1 << i)),
            tuple(i for i in range(COMPLEMENT_SIZE) if missed & (1 << i)))


def heuristic_regular_model(signatures, maximum, restarts, steps, seed):
    """Find a SAT certificate quickly; Z3 remains the exhaustive backend."""
    rng = random.Random(seed)
    catalogue = regular_catalogue()
    best = None
    best_score = math.inf
    for restart in range(restarts):
        rows = []
        root_count = {}
        for _ in range(signatures):
            choices = []
            for candidate in rng.sample(catalogue, len(catalogue)):
                if candidate in rows or root_count.get(candidate[0], 0) >= 3:
                    continue
                if all(compatible(candidate, row) for row in rows):
                    choices.append(candidate)
                    if len(choices) == 32:
                        break
            if not choices:
                break
            candidate = rng.choice(choices)
            rows.append(candidate)
            root_count[candidate[0]] = root_count.get(candidate[0], 0) + 1
        if len(rows) != signatures:
            continue
        score = witness_excess(rows, maximum)
        temperature = 2.0
        for step in range(steps):
            if score == 0:
                converted = [tuple_from_masks(row) for row in rows]
                verify(converted, maximum)
                print({"heuristic": "sat", "restart": restart,
                       "step": step, "seed": seed})
                report(converted)
                return converted
            slot = rng.randrange(signatures)
            old = rows[slot]
            others = rows[:slot] + rows[slot + 1:]
            other_root_count = {}
            for row in others:
                other_root_count[row[0]] = other_root_count.get(row[0], 0) + 1
            replacement = None
            for _ in range(256):
                candidate = rng.choice(catalogue)
                if candidate in others or other_root_count.get(candidate[0], 0) >= 3:
                    continue
                if all(compatible(candidate, row) for row in others):
                    replacement = candidate
                    break
            if replacement is None:
                continue
            rows[slot] = replacement
            new_score = witness_excess(rows, maximum)
            cooling = temperature * (1.0 - step / max(steps, 1)) + 0.01
            if new_score <= score or rng.random() < math.exp((score - new_score) / cooling):
                score = new_score
            else:
                rows[slot] = old
            if score < best_score:
                best_score = score
                best = list(rows)
        print({"heuristic_restart": restart, "best_score": best_score}, flush=True)
    if best is not None:
        print({"heuristic": "no_model", "best_score": best_score})
        report([tuple_from_masks(row) for row in best])
    return None


def run(signatures=13, max_balanced_witnesses=2, timeout_ms=0,
        regular_only=False, second_intersections=None, engine="qffd",
        regular_balance_only=False, pb_solver="solver", threads=1,
        regular_count=None, first_regular=False):
    solver, root, missed, _balance = build_solver(
        signatures, max_balanced_witnesses, timeout_ms, regular_only,
        second_intersections, engine, regular_balance_only,
        regular_count=regular_count, first_regular=first_regular)
    if engine == "qffd":
        solver.set("pb.solver", pb_solver)
        solver.set(threads=threads)
    status = solver.check()
    print({
        "status": str(status),
        "signatures": signatures,
        "max_balanced_witnesses": max_balanced_witnesses,
        "regular_only": regular_only,
        "second_intersections": second_intersections,
        "engine": engine,
        "regular_balance_only": regular_balance_only,
        "pb_solver": pb_solver,
        "threads": threads,
        "regular_count": regular_count,
        "first_regular": first_regular,
    })
    if status != sat:
        return status
    model = solver.model()
    rows = [(selected(model, root[s]), selected(model, missed[s]))
            for s in range(signatures)]
    verify(rows, max_balanced_witnesses, regular_balance_only)
    report(rows)
    return status


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--signatures", type=int, default=13)
    parser.add_argument("--max-balanced-witnesses", type=int, default=2)
    parser.add_argument("--timeout-ms", type=int, default=0)
    parser.add_argument("--regular-only", action="store_true")
    parser.add_argument("--heuristic-restarts", type=int, default=0)
    parser.add_argument("--heuristic-steps", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=466)
    parser.add_argument("--second-root-intersection", type=int)
    parser.add_argument("--second-missed-intersection", type=int)
    parser.add_argument("--engine", choices=("qffd", "smt"), default="qffd")
    parser.add_argument("--regular-balance-only", action="store_true")
    parser.add_argument("--pb-solver", choices=(
        "solver", "circuit", "sorting", "totalizer", "binary_merge",
        "segmented"), default="solver")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--regular-count", type=int)
    parser.add_argument("--first-regular", action="store_true")
    args = parser.parse_args()
    if args.heuristic_restarts:
        model = heuristic_regular_model(
            args.signatures, args.max_balanced_witnesses,
            args.heuristic_restarts, args.heuristic_steps, args.seed)
        raise SystemExit(0 if model is not None else 1)
    second = None
    if (args.second_root_intersection is None) != \
            (args.second_missed_intersection is None):
        parser.error("provide both --second-*-intersection arguments")
    if args.second_root_intersection is not None:
        second = (args.second_root_intersection,
                  args.second_missed_intersection)
    result = run(args.signatures, args.max_balanced_witnesses,
                 args.timeout_ms, args.regular_only, second, args.engine,
                 args.regular_balance_only, args.pb_solver, args.threads,
                 args.regular_count, args.first_regular)
    raise SystemExit(0 if result == sat else 1)
