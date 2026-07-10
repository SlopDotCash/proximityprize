#!/usr/bin/env python3
"""Exact CSP search for a 17-point half-predecessor line in RS[16,4]/F_17.

The evaluation domain is F_17^*.  We quotient each received row by the cubic
RS code by forcing its values on the first four domain points to zero.  Z3 then
searches for a nonzero quotient direction u1 such that, for every gamma in F_17,
u0+gamma*u1 agrees with some cubic on at least nine of the sixteen points.

A satisfying assignment is checked independently with exact modular linear
algebra.  The checker enumerates every 9-subset witness for every gamma and
reports whether each scalar has a nonjoint witness (the actual MCA condition).

This is an exact finite search for the fixed normalization, not a random probe.
The default mode tries each possible first nonzero normalized direction coordinate
as a symmetry-breaking branch.  ``--free-pivot`` uses one disjunctive branch.
"""

from argparse import ArgumentParser
from itertools import combinations
import importlib.util
from pathlib import Path

from z3 import And, Bool, If, Int, Or, PbGe, Solver, sat, unsat


P = 17
N = 16
K = 4
T = 9
GENERATOR = 3


def load_probe_helpers():
    path = Path(__file__).with_name("probe_half_radius_grassmann.py")
    spec = importlib.util.spec_from_file_location("half_radius_helpers", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def domain_and_vandermonde():
    domain = [pow(GENERATOR, i, P) for i in range(N)]
    vand = [[pow(x, j, P) for j in range(K)] for x in domain]
    return domain, vand


def residue(x):
    return x % P


def build_solver(pivot=None, timeout_ms=0):
    domain, vand = domain_and_vandermonde()
    solver = Solver()
    if timeout_ms:
        solver.set(timeout=timeout_ms)

    u0 = [Int(f"u0_{i}") for i in range(N)]
    u1 = [Int(f"u1_{i}") for i in range(N)]
    coeff = [[Int(f"f_{gamma}_{j}") for j in range(K)]
             for gamma in range(P)]
    agree = [[Bool(f"a_{gamma}_{i}") for i in range(N)]
             for gamma in range(P)]

    for value in u0 + u1 + [x for row in coeff for x in row]:
        solver.add(0 <= value, value < P)

    # Unique quotient representatives modulo the degree-<4 RS code.
    for i in range(K):
        solver.add(u0[i] == 0, u1[i] == 0)

    if pivot is None:
        solver.add(Or(*[u1[i] != 0 for i in range(K, N)]))
    else:
        # First nonzero normalized coordinate; scaling the whole direction makes
        # it one.  Trying all pivots covers every nonzero normalized direction.
        for i in range(K, pivot):
            solver.add(u1[i] == 0)
        solver.add(u1[pivot] == 1)

    for gamma in range(P):
        for i in range(N):
            polynomial = sum(coeff[gamma][j] * vand[i][j] for j in range(K))
            difference = u0[i] + gamma * u1[i] - polynomial
            solver.add(agree[gamma][i] == (difference % P == 0))
        solver.add(PbGe([(agree[gamma][i], 1) for i in range(N)], T))

    return solver, u0, u1, coeff, agree, domain


def model_vector(model, variables):
    return [model.eval(x, model_completion=True).as_long() % P for x in variables]


def enumerate_witnesses(u0, u1, domain):
    helpers = load_probe_helpers()
    witnesses = {gamma: [] for gamma in range(P)}
    maximal = {}
    for gamma in range(P):
        word = [(a + gamma * b) % P for a, b in zip(u0, u1)]
        best = 0
        best_support = None
        for support in combinations(range(N), T):
            checks = helpers.agreement_parity(domain, K, support, P)
            if not checks.any():
                continue
            if not (checks @ word % P).any():
                nonjoint = bool((checks @ u1 % P).any())
                witnesses[gamma].append((support, nonjoint))
        # Recover the maximal agreement size from the 9-witness union.  A cubic
        # fitting one 9-subset is unique, so interpolate it and count all points.
        for support, _ in witnesses[gamma]:
            base = support[:K]
            import numpy as np
            vand = np.asarray([[pow(domain[i], j, P) for j in range(K)]
                               for i in base], dtype=np.int64)
            inv = helpers.np_inverse(vand, P)
            values = np.asarray([word[i] for i in base], dtype=np.int64)
            polynomial_coeff = inv @ values % P
            agreement = tuple(i for i, x in enumerate(domain)
                              if sum(int(polynomial_coeff[j]) * pow(x, j, P)
                                     for j in range(K)) % P == word[i])
            if len(agreement) > best:
                best, best_support = len(agreement), agreement
        maximal[gamma] = (best, best_support)
    return witnesses, maximal


def check_model(model, u0vars, u1vars, agreevars, domain, pivot):
    u0 = model_vector(model, u0vars)
    u1 = model_vector(model, u1vars)
    claimed = {
        gamma: tuple(i for i in range(N)
                     if bool(model.eval(agreevars[gamma][i], model_completion=True)))
        for gamma in range(P)
    }
    assert all(len(support) >= T for support in claimed.values())
    witnesses, maximal = enumerate_witnesses(u0, u1, domain)
    nonjoint = {gamma: [support for support, proper in rows if proper]
                for gamma, rows in witnesses.items()}
    result = {
        "pivot": pivot,
        "u0": u0,
        "u1": u1,
        "claimed_agreements": claimed,
        "witness_multiplicities": {g: len(rows) for g, rows in witnesses.items()},
        "nonjoint_multiplicities": {g: len(rows) for g, rows in nonjoint.items()},
        "maximal_agreements": maximal,
        "all_17_have_witness": all(witnesses[g] for g in range(P)),
        "all_17_nonjoint": all(nonjoint[g] for g in range(P)),
    }
    print(result, flush=True)
    return result


def run(free_pivot=False, timeout_ms=0):
    pivots = [None] if free_pivot else list(range(K, N))
    outcomes = []
    for pivot in pivots:
        solver, u0, u1, _coeff, agree, domain = build_solver(pivot, timeout_ms)
        status = solver.check()
        print({"pivot": pivot, "status": str(status)}, flush=True)
        if status == sat:
            result = check_model(solver.model(), u0, u1, agree, domain, pivot)
            outcomes.append((pivot, "sat", result["all_17_nonjoint"]))
            if result["all_17_nonjoint"]:
                print("MCA_COUNTEREXAMPLE", result, flush=True)
                return False
        elif status == unsat:
            outcomes.append((pivot, "unsat", False))
        else:
            outcomes.append((pivot, "unknown", False))
    print({"outcomes": outcomes}, flush=True)
    return True


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--free-pivot", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=0)
    args = parser.parse_args()
    raise SystemExit(0 if run(args.free_pivot, args.timeout_ms) else 1)
