#!/usr/bin/env python3
"""
hd2_ledger_projection.py — HEURISTIC projection of the PR #122 seed ledger to d = 2
(sparse `s₂ ≤ 1` family), to size the payoff of the real geometric port.

Classification (dossier v4 §6): HEURISTIC ESTIMATE.  The d = 1 ledger's branch shapes
(whole/cut/singular) encode specific incidence geometry proven in the better.codes Lean
development at its profile; here each branch is extended by one agreement-vector slot for
the extra derivative variable R₂ (weight ≈ w, degree cap s₂) — a SHAPE ASSUMPTION, not a
theorem.  The output says whether porting the geometry is worth it, nothing more.

Interpolation gate: EXACT (hd_general_rank.node_rank at d = 2, line setting), so the radius
side of every row is sound; only the seed side is heuristic.

Usage: python3 hd2_ledger_projection.py
"""
import math
import sys
import os
from itertools import permutations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hd_general_rank import node_rank, dim_space  # noqa: E402


def mixed4(a, b, c, d):
    """Coefficient of UVWX in the product of four linear forms with coefficient vectors
    a, b, c, d (each of length 4)."""
    tot = 0
    for p in permutations(range(4)):
        tot += a[p[0]] * b[p[1]] * c[p[2]] * d[p[3]]
    return tot


U_Y, U_R1, U_R2, U_Z = (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)


def ledger2(n, w, a, m, s1, s2, L):
    """Heuristic d=2 ledger: every d=1 branch gains one E-slot for R₂."""
    D = m * a
    yCap = (D - 1) // w
    gap = a - w
    e = n - a
    j = ((2 * s1 - 1) + (2 * s2 - 1)) * L
    E = (1 + 2 * w * yCap, w * (2 * s1 - 1), w * max(1, 2 * s2 - 1), 2 * w * L + 1)
    tail = lambda h: (1 + 2 * h * yCap, h * (2 * s1 - 1), h * max(1, 2 * s2 - 1), 2 * h * L)
    first, last = tail(w + 1), tail(D)

    def whole(v):
        return (n * (n - w) * mixed4(v, E, E, E)
                + (e + 1) * (n - w) * gap * mixed4(v, E, E, U_Z))

    def cut(v):
        return (gap ** 2 * mixed4(v, first, last, E) + n * gap * mixed4(v, first, E, E)
                + (e + 1) * gap ** 2 * mixed4(v, first, E, U_Z))
    regular = (yCap * max(cut(U_Y), whole(U_Y)) + s1 * max(cut(U_R1), whole(U_R1))
               + max(1, s2) * max(cut(U_R2), whole(U_R2))
               + L * max(cut(U_Z), whole(U_Z)))
    singular = (gap * (j + 2 * j * j + j * (1 + 2 * (w + 1) * (j - 1)) + (e + 1) * j)
                + n * j * (1 + 2 * w * (j - 1)))
    total = regular + gap * singular
    return total, gap


def sparse_cap(s1, s1p):
    """The s₂ ≤ 1 family: {(b1, 0): b1 <= s1} ∪ {(b1, 1): b1 <= s1p}."""
    return ((s1, 1), lambda bs, a=s1, b=s1p: bs[1] == 0 or bs[0] <= b)


def interpolation_ok(n, w, a, m, s1, s1p, L):
    k = w + 1
    D = m * a
    cap = sparse_cap(s1, s1p)
    return dim_space(2, w, D, cap, L) > n * node_rank(2, m, w, D, cap, L)


def certify(n, w, a, m, s1, s1p, L, budget):
    total, gap = ledger2(n, w, a, m, s1, max(1, 1), L)
    if total >= budget * gap * gap:
        return False, None
    if not interpolation_ok(n, w, a, m, s1, s1p, L):
        return False, None
    return True, math.log2(max(2, total // (gap * gap)))


def main():
    print("== d=2 sparse-family ledger PROJECTION (heuristic seed side, exact radius side)")
    print("   budget 2^122 (|F| ~ 2^250, eps* = 2^-128)")
    for nexp in (18, 24, 30):
        n = 1 << nexp
        w = (1 << (nexp - 1)) - 1
        budget = 1 << 122
        best = None
        for m in (12, 13, 14, 16):
            for s1 in (3, 4, 5):
                for s1p in (1, 2, 3):
                    if s1p > s1:
                        continue
                    for L in (120, 169, 220, 300):
                        lo, hi = w + 2, n
                        # bisect the least certified a
                        def ok(a):
                            c, _ = certify(n, w, a, m, s1, s1p, L, budget)
                            return c
                        if not ok(hi):
                            continue
                        while lo < hi:
                            mid = (lo + hi) // 2
                            if ok(mid):
                                hi = mid
                            else:
                                lo = mid + 1
                        a = lo
                        if best is None or a < best[0]:
                            best = (a, m, s1, s1p, L)
                            print(f"  n=2^{nexp}: a={a} delta={1 - a / n:.5f} "
                                  f"(m={m} s1={s1} s1'={s1p} L={L})", flush=True)
        if best:
            a, m, s1, s1p, L = best
            print(f"  BEST n=2^{nexp}: delta={1 - a / n:.5f} (d=1 row was 0.30896)", flush=True)


if __name__ == "__main__":
    main()
