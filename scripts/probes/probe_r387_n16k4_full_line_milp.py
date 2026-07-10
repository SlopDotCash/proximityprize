#!/usr/bin/env python3
"""MILP falsification gate for a full affine line in RS[16,4]/F_17.

This encodes the same finite problem as ``probe_r387_n16k4_full_line_z3.py``
as a mixed-integer linear feasibility problem.  A Boolean ``a[g,i]`` says that
the word ``u0+g*u1`` agrees at coordinate ``i`` with a cubic ``f_g``.  If it is
one, an integer quotient ``z[g,i]`` enforces the exact congruence

    u0[i] + g*u1[i] - f_g(x_i) = 17*z[g,i].

At least nine agreement Booleans are required for every g in F_17.  Both rows
are normalized modulo the cubic RS code by setting their first four values to
zero.  A pivot branch fixes the first nonzero remaining coordinate of u1 to one;
the twelve branches exhaust all nonzero normalized directions up to scaling.

Every feasible solution is independently checked by enumerating all 9-subset
witnesses and testing the nonjoint clause.
"""

from argparse import ArgumentParser
import importlib.util
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix


P = 17
N = 16
K = 4
T = 9
GENERATOR = 3
BIG_M = 16


def load_checker():
    path = Path(__file__).with_name("probe_r387_n16k4_full_line_z3.py")
    spec = importlib.util.spec_from_file_location("r387_z3_checker", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Layout:
    def __init__(self):
        cursor = 0
        self.u0 = np.arange(cursor, cursor + N); cursor += N
        self.u1 = np.arange(cursor, cursor + N); cursor += N
        self.f = np.arange(cursor, cursor + P * K).reshape(P, K); cursor += P * K
        self.a = np.arange(cursor, cursor + P * N).reshape(P, N); cursor += P * N
        self.z = np.arange(cursor, cursor + P * N).reshape(P, N); cursor += P * N
        self.size = cursor


def normalized_monomial_direction(exponent, domain):
    """x^exponent modulo the unique cubic matching its first four values."""
    checker = load_checker()
    values = np.asarray([pow(x, exponent, P) for x in domain], dtype=np.int64)
    vand = np.asarray([[pow(domain[i], j, P) for j in range(K)]
                       for i in range(K)], dtype=np.int64)
    cubic = checker.load_probe_helpers().np_inverse(vand, P) @ values[:K] % P
    return np.asarray([
        (int(values[i]) - sum(int(cubic[j]) * pow(domain[i], j, P)
                              for j in range(K))) % P
        for i in range(N)
    ], dtype=np.int64)


def build_problem(pivot=None, time_limit=None, random_seed=20260723,
                  fixed_direction=None):
    checker = load_checker()
    domain, vand = checker.domain_and_vandermonde()
    vand = np.asarray(vand, dtype=np.int64)
    layout = Layout()

    lower = np.full(layout.size, -64.0)
    upper = np.full(layout.size, 64.0)
    lower[np.r_[layout.u0, layout.u1, layout.f.ravel()]] = 0
    upper[np.r_[layout.u0, layout.u1, layout.f.ravel()]] = P - 1
    lower[layout.a.ravel()] = 0
    upper[layout.a.ravel()] = 1
    for i in range(K):
        lower[layout.u0[i]] = upper[layout.u0[i]] = 0
        lower[layout.u1[i]] = upper[layout.u1[i]] = 0
    if fixed_direction is not None:
        for i, value in enumerate(fixed_direction):
            lower[layout.u1[i]] = upper[layout.u1[i]] = int(value)
    else:
        if pivot is None:
            raise ValueError("pivot is required when direction is not fixed")
        for i in range(K, pivot):
            lower[layout.u1[i]] = upper[layout.u1[i]] = 0
        lower[layout.u1[pivot]] = upper[layout.u1[pivot]] = 1

    row_count = 2 * P * N + P
    matrix = lil_matrix((row_count, layout.size), dtype=np.float64)
    lhs = np.full(row_count, -np.inf)
    rhs = np.full(row_count, np.inf)
    row = 0
    for gamma in range(P):
        for i in range(N):
            # e = u0_i + gamma*u1_i - f_gamma(x_i) - 17*z_gamma_i.
            terms = {
                int(layout.u0[i]): 1,
                int(layout.u1[i]): gamma,
                int(layout.z[gamma, i]): -P,
            }
            for j in range(K):
                index = int(layout.f[gamma, j])
                terms[index] = terms.get(index, 0) - int(vand[i, j])
            # e + M*a <= M and -e + M*a <= M.  Thus a=1 forces e=0;
            # when a=0, an integer quotient can always arrange |e|<=8.
            for index, value in terms.items():
                matrix[row, index] = value
            matrix[row, layout.a[gamma, i]] = BIG_M
            rhs[row] = BIG_M
            row += 1
            for index, value in terms.items():
                matrix[row, index] = -value
            matrix[row, layout.a[gamma, i]] = BIG_M
            rhs[row] = BIG_M
            row += 1
        matrix[row, layout.a[gamma]] = -1
        rhs[row] = -T
        row += 1
    assert row == row_count

    # A tiny deterministic objective breaks degeneracy without changing feasibility.
    rng = np.random.default_rng(random_seed + (pivot or 0))
    objective = np.zeros(layout.size)
    objective[layout.u0] = rng.integers(0, 5, size=N)
    objective[layout.u1] = rng.integers(0, 5, size=N)
    options = {"disp": True, "mip_rel_gap": 0.0}
    if time_limit:
        options["time_limit"] = float(time_limit)
    return (objective, np.ones(layout.size, dtype=np.int8),
            Bounds(lower, upper), LinearConstraint(matrix.tocsr(), lhs, rhs),
            options, layout, domain)


def extract_and_check(solution, layout, domain, pivot):
    checker = load_checker()
    rounded = np.rint(solution).astype(np.int64)
    assert np.max(np.abs(solution - rounded)) < 1e-6
    u0 = [int(x) % P for x in rounded[layout.u0]]
    u1 = [int(x) % P for x in rounded[layout.u1]]
    witnesses, maximal = checker.enumerate_witnesses(u0, u1, domain)
    nonjoint = {gamma: [support for support, proper in rows if proper]
                for gamma, rows in witnesses.items()}
    result = {
        "pivot": pivot,
        "u0": u0,
        "u1": u1,
        "witness_multiplicities": {g: len(rows) for g, rows in witnesses.items()},
        "nonjoint_multiplicities": {g: len(rows) for g, rows in nonjoint.items()},
        "maximal_agreements": maximal,
        "all_17_have_witness": all(witnesses[g] for g in range(P)),
        "all_17_nonjoint": all(nonjoint[g] for g in range(P)),
    }
    print(result, flush=True)
    return result


def run(pivots, time_limit=None, monomial=None):
    summary = []
    checker = load_checker()
    domain, _ = checker.domain_and_vandermonde()
    fixed_direction = None
    if monomial is not None:
        fixed_direction = normalized_monomial_direction(monomial, domain)
        print({"monomial": monomial,
               "normalized_direction": fixed_direction.tolist()}, flush=True)
    for pivot in pivots:
        problem = build_problem(pivot, time_limit=time_limit,
                                fixed_direction=fixed_direction)
        result = milp(c=problem[0], integrality=problem[1], bounds=problem[2],
                      constraints=problem[3], options=problem[4])
        status = {0: "optimal", 1: "limit", 2: "infeasible", 3: "unbounded",
                  4: "other"}.get(result.status, str(result.status))
        print({"pivot": pivot, "status": status, "message": result.message,
               "nodes": getattr(result, "mip_node_count", None)}, flush=True)
        if result.x is not None:
            checked = extract_and_check(result.x, problem[5], problem[6], pivot)
            summary.append((pivot, status, checked["all_17_nonjoint"]))
            if checked["all_17_nonjoint"]:
                print("MCA_COUNTEREXAMPLE", checked, flush=True)
                return False
        else:
            summary.append((pivot, status, False))
    print({"summary": summary}, flush=True)
    return True


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--pivot", type=int, action="append")
    parser.add_argument("--time-limit", type=float)
    parser.add_argument("--monomial", type=int)
    args = parser.parse_args()
    pivots = args.pivot if args.pivot else (
        [None] if args.monomial is not None else list(range(K, N)))
    if any(pivot is not None and (pivot < K or pivot >= N) for pivot in pivots):
        parser.error(f"pivot must lie in [{K},{N - 1}]")
    raise SystemExit(0 if run(pivots, args.time_limit, args.monomial) else 1)
