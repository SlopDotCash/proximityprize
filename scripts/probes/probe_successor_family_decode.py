#!/usr/bin/env python3
"""Exhaustive decoding of one four-head family reported by the successor census.

`probe_successor_four_head_census.cpp` prints families as three site masks and two
constants. This script rebuilds the heads f_0 = V_{Z0}, f_1 = l1 V_{Z1}, f_2 = l2 V_{Z2},
f_3 = 0, chooses the received scalar row with four cores of size 3h-2 and the most bad
scalars, lifts it with the direction (X, 1), and counts by exhaustive decoding the
scalars z for which u + z v agrees with a codeword of dimension 2h on at least 3h-1 sites
without a joint explanation of (u, v) there.

    python3 probe_successor_family_decode.py 4 97 8 00e301 002465 00c624 24 33

That family over F_97 is reported with 19 scalars on 16 sites. Needs numpy.
"""
from itertools import combinations, product
import sys

import numpy as np


def main():
    h, p, g = (int(x) for x in sys.argv[1:4])
    z0, z1, z2 = (int(x, 16) for x in sys.argv[4:7])
    l1, l2 = int(sys.argv[7]), int(sys.argv[8])
    n, k, t, rich = 4 * h, 2 * h, 3 * h - 1, 3 * h - 2
    root = [pow(g, e, p) for e in range(n)]
    inv = [0] + [pow(a, p - 2, p) for a in range(1, p)]

    def vanish(mask, x):
        out = 1
        for s in range(n):
            if mask >> s & 1:
                out = out * (x - root[s]) % p
        return out

    heads = [[vanish(z0, x) for x in root], [l1 * vanish(z1, x) % p for x in root],
             [l2 * vanish(z2, x) % p for x in root], [0] * n]

    # per-site options: (core membership as a tuple, received value or None, gain)
    options = []
    for e in range(n):
        values = sorted({heads[i][e] for i in range(4)})
        site = [(tuple(int(heads[i][e] == v) for i in range(4)), v) for v in values]
        options.append([(m, v, 0 if sum(m) == 4 else 1) for m, v in site]
                       + [((0, 0, 0, 0), None, 4)])
    best = {(0, 0, 0, 0): (0, [])}
    for e in range(n):
        new = {}
        for state, (gain, choice) in best.items():
            for m, v, extra in options[e]:
                s = tuple(min(rich, state[i] + m[i]) for i in range(4))
                if s not in new or new[s][0] < gain + extra:
                    new[s] = (gain + extra, choice + [v])
        best = new
    target = (rich,) * 4
    if target not in best:
        print("no assignment with four cores of size", rich)
        return
    predicted, y = best[target]
    covered = [e for e in range(n) if y[e] is not None]
    holes = [e for e in range(n) if y[e] is None]

    sets = np.array(list(combinations(range(n), k)), dtype=np.int64)
    comp = np.array([[e for e in range(n) if e not in set(row)] for row in sets], dtype=np.int64)
    roots, invs = np.array(root, dtype=np.int64), np.array(inv, dtype=np.int64)
    xt, xc = roots[sets], roots[comp]
    full = np.ones(xc.shape, dtype=np.int64)
    for i in range(k):
        full = full * ((xc - xt[:, i:i + 1]) % p) % p
    denom = np.ones(xt.shape, dtype=np.int64)
    for i in range(k):
        d = (xt - xt[:, i:i + 1]) % p
        d[:, i] = 1
        denom = denom * d % p
    M = full[:, :, None] * invs[(xc[:, :, None] - xt[:, None, :]) % p] % p * invs[denom][:, None, :] % p

    def count(hole_values):
        u = np.zeros(n, dtype=np.int64)
        v = np.zeros(n, dtype=np.int64)
        for e in covered:
            u[e], v[e] = root[e] * y[e] % p, y[e]
        for e, (ub, vb) in zip(holes, hole_values):
            u[e], v[e] = ub, vb
        pu = np.einsum("tcj,tj->tc", M, u[sets]) % p
        pv = np.einsum("tcj,tj->tc", M, v[sets]) % p
        bad = 0
        for z in range(p):
            w = (u + z * v) % p
            agree = (pu + z * pv) % p == w[comp]
            enough = agree.sum(axis=1) >= t - k
            joint = ((pu == u[comp]) & (pv == v[comp])) | ~agree
            bad += bool((enough & ~joint.all(axis=1)).any())
        return bad

    most = 0
    for hole_values in product(product(range(p), range(1, p)), repeat=len(holes)):
        most = max(most, count(hole_values))
        if most >= predicted or len(holes) > 1:
            break
    print(f"h = {h}, p = {p}: predicted {predicted} bad scalars, exhaustive decoding finds "
          f"{most}; {n} sites, {len(holes)} uncovered")


if __name__ == "__main__":
    main()
