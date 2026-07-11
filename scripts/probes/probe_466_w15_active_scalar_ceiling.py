#!/usr/bin/env python3
"""Probe (#466, lane W15 part 5): is L_near^true = 2 in the refuted regime / window?

Part 4 refuted L_near = 1 (two-block lines, 3a <= 2n).  This probe decides whether 2 is a
ceiling:

  Q1. Multi-constant-block ladder: M blocks of size b with M distinct offset constants,
      support = everything else with offset 0.  Constant c = gamma_j appears at
      gamma = gamma_j with agreement b + (n - M*b) = n - (M-1)*b >= a.  Constraints:
      M*b >= a (large-zero), n - (M-1)*b >= a (appearance), M*(k-1) < a (safety for
      non-constants), b <= a - 1, q >= M.  At (11,10,2,6): M=3, b=2 fits => Lambda >= 3.
      At (17,16,4,9): M*(k-1) < a forces M <= 2 for CONSTANT blocks.
  Q2. Non-constant three-piece attempt at the campaign shape (17,16,4,9): three
      codewords c1=0, c2, c3 with matched support differences and overlapping Z-blocks
      (pairwise codeword agreements serve two blocks at once).  Feasible iff
      3*7 - (pairwise Z-overlaps) <= z = 14, i.e. overlaps >= 7 <= 9 = 3*(k-1).
  Q3. Randomized hill-climb on u0 at (17,16,4,9) (z = 14 and z = 9), maximizing Lambda
      subject to safe + large-zero.

Deterministic (seeded).  Exit 0 iff Q1's 3-block construction verifies at (11,10,2,6).
"""

import itertools
import sys

import numpy as np

rng = np.random.default_rng(466_155)


def all_codewords(q, n, k):
    dom = np.arange(n)
    V = np.vstack([np.array([pow(int(x), j, q) for x in dom]) for j in range(k)])
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))
    return (coeffs @ V) % q


def stats(q, n, k, a, CW, u0, u1):
    Z = np.where(u1 % q == 0)[0]
    agrZ = (CW[:, Z] == u0[Z][None, :]).sum(axis=1) if len(Z) else np.zeros(len(CW), int)
    safe = bool(agrZ.max(initial=0) < a)
    lz = bool(len(Z) >= a)
    appearing = set()
    for g in range(q):
        line = (u0 + g * u1) % q
        agr = (CW == line[None, :]).sum(axis=1)
        appearing.update(np.where(agr >= a)[0].tolist())
    return lz, safe, len(appearing)


def multiblock(q, n, a, M, b):
    u1 = np.ones(n, dtype=int)
    u1[:M * b] = 0
    u0 = np.zeros(n, dtype=int)
    for j in range(M):
        u0[j * b:(j + 1) * b] = j  # constants 0..M-1 (q >= M)
    return u0, u1


def main():
    ok = False

    # Q1a: (11,10,2,6) with M=3, b=2
    q, n, k, a = 11, 10, 2, 6
    CW = all_codewords(q, n, k)
    u0, u1 = multiblock(q, n, a, 3, 2)
    lz, safe, lam = stats(q, n, k, a, CW, u0, u1)
    print(f"(11,10,2,6) 3-constant-block: large_zero={lz} safe={safe} Lambda={lam}")
    ok = lz and safe and lam >= 3
    # try M=4,5 variants and hill-climb for more
    best = lam if (lz and safe) else 0
    for M, b in [(4, 2), (5, 2), (3, 3), (4, 3)]:
        if M * b > n - 1:
            continue
        u0m, u1m = multiblock(q, n, a, M, b)
        lzm, sm, lm = stats(q, n, k, a, CW, u0m, u1m)
        print(f"(11,10,2,6) M={M},b={b}: large_zero={lzm} safe={sm} Lambda={lm}")
        if lzm and sm:
            best = max(best, lm)
    # hill-climb at (11,10,2,6), z = 6
    u1h = np.ones(n, dtype=int); u1h[:6] = 0
    cur = rng.integers(0, q, size=n); curL = -1
    for it in range(400):
        cand = cur.copy()
        for _ in range(int(rng.integers(1, 3))):
            cand[int(rng.integers(n))] = int(rng.integers(q))
        lzc, sc, lc = stats(q, n, k, a, CW, cand, u1h)
        if lzc and sc and lc >= curL:
            cur, curL = cand, lc
    print(f"(11,10,2,6) hill-climb z=6: best Lambda={curL}")
    best = max(best, curL)
    print(f"(11,10,2,6): MAX safe large-zero Lambda found = {best}\n")

    # Q2/Q3: campaign shape
    q, n, k, a = 17, 16, 4, 9
    CW = all_codewords(q, n, k)
    best9 = 0
    # structured three-piece: c1 = 0, sample c2, c3 with c(i14)=c(i15), overlaps >= 7
    dom = np.arange(n)
    tries = 0
    for _ in range(4000):
        co2 = rng.integers(0, q, size=k)
        co3 = rng.integers(0, q, size=k)
        c2 = np.array([sum(int(co2[j]) * pow(int(x), j, q) for j in range(k)) % q
                       for x in dom])
        c3 = np.array([sum(int(co3[j]) * pow(int(x), j, q) for j in range(k)) % q
                       for x in dom])
        if c2[14] != c2[15] or c3[14] != c3[15]:
            continue
        if (c2 == 0).all() or (c3 == 0).all() or (c2 == c3).all():
            continue
        Zpts = np.arange(14)
        A12 = [i for i in Zpts if c2[i] == 0]
        A13 = [i for i in Zpts if c3[i] == 0]
        A23 = [i for i in Zpts if c2[i] == c3[i]]
        ov = len(set(A12)) + len(set(A13)) + len(set(A23) - set(A12) - set(A13))
        if 21 - ov > 14:
            continue
        tries += 1
        # greedy assignment: each codeword needs 7 Z-points; overlap points serve 2
        u0c = np.full(n, -1, dtype=int)
        need = {1: 7, 2: 7, 3: 7}
        vals = {1: np.zeros(n, dtype=int), 2: c2, 3: c3}
        pair_of = ([(i, (1, 2)) for i in A12] + [(i, (1, 3)) for i in A13]
                   + [(i, (2, 3)) for i in A23 if i not in A12 and i not in A13])
        used = set()
        for i, (x, y) in pair_of:
            if i in used or (need[x] <= 0 and need[y] <= 0):
                continue
            u0c[i] = vals[x][i]
            need[x] -= 1; need[y] -= 1
            used.add(i)
        for i in Zpts:
            if i in used:
                continue
            for j in (1, 2, 3):
                if need[j] > 0:
                    u0c[i] = vals[j][i]; need[j] -= 1; used.add(i)
                    break
            else:
                u0c[i] = int(rng.integers(q))
        if max(need.values()) > 0:
            continue
        u0c[14] = 0; u0c[15] = 0
        u1c = np.zeros(n, dtype=int); u1c[14:] = 1
        lzc, sc, lc = stats(q, n, k, a, CW, u0c % q, u1c)
        if lzc and sc:
            best9 = max(best9, lc)
            if lc >= 3:
                print(f"(17,16,4,9) structured three-piece FOUND Lambda={lc} (safe)")
                break
    print(f"(17,16,4,9) structured search: {tries} feasible triples tried, "
          f"best safe Lambda={best9}")
    # hill-climb at z = 14 and z = 9
    for z in (14, 9):
        u1h = np.zeros(n, dtype=int); u1h[z:] = 1
        cur = rng.integers(0, q, size=n); curL = -1
        for it in range(300):
            cand = cur.copy()
            for _ in range(int(rng.integers(1, 3))):
                cand[int(rng.integers(n))] = int(rng.integers(q))
            lzc, sc, lc = stats(q, n, k, a, CW, cand, u1h)
            if lzc and sc and lc >= curL:
                cur, curL = cand, lc
        print(f"(17,16,4,9) hill-climb z={z}: best Lambda={curL}")
        best9 = max(best9, curL)
    print(f"(17,16,4,9): MAX safe large-zero Lambda found = {best9}")

    print()
    if ok:
        print("RESULT: 3-constant-block VERIFIED at (11,10,2,6) — L_near = 2 is NOT a "
              "universal ceiling; the constant-block ladder is shape-dependent")
        return 0
    print("RESULT: 3-block construction failed")
    return 1


if __name__ == "__main__":
    sys.exit(main())
