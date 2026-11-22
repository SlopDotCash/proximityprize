#!/usr/bin/env python3
"""Brute-force check of the common-remainder converse at h = 5 over F_41.

`probe_successor_common_remainder.cpp 5 41 36` reports nine configurations over F_41, a
small-field accident: no prime from 61 to 661 has any. This script takes the first one,
builds the four heads and the received pair (u, v), and counts by exhaustive decoding the
scalars z for which u + z v agrees with a codeword of the dimension-10 Reed-Solomon code
on at least 14 of the 20 sites while (u, v) is not jointly explained on that agreement
set. The count is 23 = n + 3: all 19 covered sites and four scalars at the uncovered site.

    python3 probe_successor_converse_check.py     # about a minute, needs numpy
"""
from itertools import combinations
import sys

import numpy as np

P, H, G = 41, 5, 36
N, K, T = 4 * H, 2 * H, 3 * H - 1
S3, S0, S1, S2 = [0, 1, 2], [3, 4, 7, 17], [5, 15, 18, 19], [8, 10, 12, 14]
R01, R02, R12 = 11, 16, 6
ROOT = [pow(G, e, P) for e in range(N)]
INV = [0] + [pow(a, P - 2, P) for a in range(1, P)]


def vanish(sites, x):
    out = 1
    for s in sites:
        out = out * (x - ROOT[s]) % P
    return out


def line_through(points):
    (x1, y1), (x2, y2) = points[0], points[1]
    a = (y2 - y1) * INV[(x2 - x1) % P] % P
    b = (y1 - a * x1) % P
    assert all((a * x + b - y) % P == 0 for x, y in points)
    return a, b


def main():
    rest = [e for e in range(N) if e not in S0 + S1 + S2 + S3 + [R01, R02, R12]]
    assert len(rest) == 2
    single, hole = rest
    g = lambda sites: [(ROOT[e], -vanish(S0, ROOT[e]) * INV[vanish(S3, ROOT[e])] % P)
                       for e in sites]
    a1, b1 = line_through(g(S1))
    a2, b2 = line_through(g(S2))
    assert (a1 * ROOT[R01] + b1) % P == 0 and (a2 * ROOT[R02] + b2) % P == 0
    assert ((a1 - a2) * ROOT[R12] + b1 - b2) % P == 0
    k1, k2 = (1 + a1) % P, (1 + a2) % P
    assert k1 and k2
    heads = [
        lambda x: k1 * vanish(S1, x) * vanish(S2, x) % P,
        lambda x: vanish(S0, x) * vanish(S2, x) % P,
        lambda x: k1 * INV[k2] * vanish(S0, x) * vanish(S1, x) % P,
        lambda x: 0,
    ]
    y = {}
    for e in S0 + S1 + S2 + [single]:
        y[e] = 0
    for e in S3:
        y[e] = heads[0](ROOT[e])
        assert heads[1](ROOT[e]) == y[e] == heads[2](ROOT[e])
    for e, (a, b) in ((R01, (0, 1)), (R02, (0, 2)), (R12, (1, 2))):
        y[e] = heads[a](ROOT[e])
        assert heads[b](ROOT[e]) == y[e]
    cores = [[e for e in y if heads[i](ROOT[e]) == y[e]] for i in range(4)]
    assert [len(c) for c in cores] == [3 * H - 2] * 4, [len(c) for c in cores]

    # all information sets and their extension matrices
    sets = np.array(list(combinations(range(N), K)), dtype=np.int64)
    comp = np.array([[e for e in range(N) if e not in set(row)] for row in sets], dtype=np.int64)
    roots = np.array(ROOT, dtype=np.int64)
    inv = np.array(INV, dtype=np.int64)
    xt, xc = roots[sets], roots[comp]                      # (nT, K), (nT, N-K)
    full = np.ones(xc.shape, dtype=np.int64)
    for i in range(K):
        full = full * ((xc - xt[:, i:i + 1]) % P) % P      # prod_i (x_c - t_i)
    denom = np.ones(xt.shape, dtype=np.int64)
    for i in range(K):
        d = (xt - xt[:, i:i + 1]) % P
        d[:, i] = 1
        denom = denom * d % P                              # prod_{i != j} (t_j - t_i)
    M = full[:, :, None] * inv[(xc[:, :, None] - xt[:, None, :]) % P] % P * inv[denom][:, None, :] % P

    def count(ub, vb):
        u = np.array([ROOT[e] * y[e] % P if e in y else ub for e in range(N)], dtype=np.int64)
        v = np.array([y[e] if e in y else vb for e in range(N)], dtype=np.int64)
        pu = np.einsum("tcj,tj->tc", M, u[sets]) % P
        pv = np.einsum("tcj,tj->tc", M, v[sets]) % P
        bad = []
        for z in range(P):
            w = (u + z * v) % P
            pw = (pu + z * pv) % P
            agree = pw == w[comp]
            rich = agree.sum(axis=1) >= T - K
            joint = ((pu == u[comp]) & (pv == v[comp])) | ~agree
            if (rich & ~joint.all(axis=1)).any():
                bad.append(z)
        return bad

    covered = sorted((-ROOT[e]) % P for e in y)
    best = None
    for ub in range(P):
        for vb in range(1, P):
            bad = count(ub, vb)
            if best is None or len(bad) > len(best[0]):
                best = (bad, ub, vb)
            if len(bad) >= N + 3:
                break
        if best and len(best[0]) >= N + 3:
            break
    bad, ub, vb = best
    print(f"h = {H}, p = {P}: {len(bad)} bad scalars with received values ({ub}, {vb}) at the "
          f"uncovered site; budget analogue n = {N}")
    print("covered-site scalars all bad:", set(covered) <= set(bad), "count", len(covered))
    sys.stdout.flush()


if __name__ == "__main__":
    main()
