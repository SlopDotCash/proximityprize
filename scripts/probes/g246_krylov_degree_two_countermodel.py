#!/usr/bin/env python3
"""G246: exact degree-two Krylov countermodel for the quotient-incidence route.

Builds the sponsor cell (n,p,m)=(8,1009,126), the symmetric quotient-incidence matrix
N[A,B]=#{x in A : 2-x in B}, and the centered rank-6 quotient profile R6^c.  It then finds a
4x4 minor of [e0^c, N e0^c, N^2 e0^c, R6^c] with nonzero determinant.  This is the exact data
certified in _G246KrylovDegreeTwoCountermodel.lean.
"""
from __future__ import annotations

import itertools
import math

import sympy as sp


def factors(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fs = factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(p)


def setup(p: int, n: int):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    logs = [0] * p
    x = 1
    for j in range(p - 1):
        logs[x] = j
        x = x * g % p
    G = [pow(g, m * j, p) for j in range(n)]
    return m, g, logs, G


def incidence(p: int, m: int, logs: list[int]) -> sp.Matrix:
    N = [[0] * m for _ in range(m)]
    for x in range(1, p):
        y = (2 - x) % p
        if y:
            N[logs[x] % m][logs[y] % m] += 1
    assert N == [list(row) for row in zip(*N)]
    return sp.Matrix(N)


def subset_profiles(p: int, G: list[int], rmax: int) -> list[list[int]]:
    dp = [[0] * p for _ in range(rmax + 1)]
    dp[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for r in range(min(rmax, used), 0, -1):
            prev, cur = dp[r - 1], dp[r]
            for t, v in enumerate(prev):
                if v:
                    cur[(t + x) % p] += v
    for r in range(rmax + 1):
        assert sum(dp[r]) == math.comb(len(G), r)
    return dp


def quotient_value(profile: list[int], p: int, m: int, g: int) -> sp.Matrix:
    vals = [profile[pow(g, a, p)] for a in range(m)]
    # The profile is constant on quotient classes in the cells used here.
    for a, want in enumerate(vals):
        for j in range(1, (p - 1) // m):
            assert profile[pow(g, a + m * j, p)] == want
    return sp.Matrix(vals)


def main() -> None:
    n, p, r, degree = 8, 1009, 6, 2
    m, g, logs, G = setup(p, n)
    assert 2 not in set(G)
    N = incidence(p, m, logs)
    dp = subset_profiles(p, G, 6)
    R = quotient_value(dp[r], p, m, g)

    one = sp.ones(m, 1)
    e0 = sp.zeros(m, 1)
    e0[0] = 1
    seed = m * e0 - one
    Rc = m * R - sum(R) * one

    cols = []
    v = seed
    for _ in range(degree + 1):
        cols.append(v)
        v = N * v
    cols.append(Rc)
    M = sp.Matrix.hstack(*cols)

    rank_seed = sp.Matrix.hstack(*cols[:-1]).rank()
    rank_aug = M.rank()
    assert rank_seed == 3
    assert rank_aug == 4

    rows = (0, 1, 2, 4)
    minor = M[list(rows), :]
    det = int(minor.det())
    assert det == -285768

    for rr in (5, 6):
        Rr = quotient_value(dp[rr], p, m, g)
        cquot = n * sum(int(N[0, a]) * int(Rr[a]) for a in range(m))
        A = p * cquot - n * n * math.comb(n, rr)
        print(f"A{rr}={A}")
    print(f"cell n={n} p={p} m={m} r={r} degree={degree}")
    print(f"rank_seed={rank_seed} rank_augmented={rank_aug}")
    print(f"minor_rows={rows} det={det}")
    print("minor=")
    for row in minor.tolist():
        print(row)
    print("PASS: R6^c is not in span{e0^c, N e0^c, N^2 e0^c} in this sponsor cell")


if __name__ == "__main__":
    main()
