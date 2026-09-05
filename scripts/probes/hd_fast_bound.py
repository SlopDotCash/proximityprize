#!/usr/bin/env python3
"""
hd_fast_bound.py — a counting-only SOUND upper bound on the per-node constraint rank of the
order-d hidden-derivative interpolant, and the resulting (sufficient) interpolation threshold.

The node map is block-diagonal over the invariants g1 = b0 + sum_j b_j, g2 = a - sum_j j*b_j
(hd_general_rank.py).  Inside a block the rank is at most min(#rows, #cols), where rows are
indexed by (i, b, e_1..e_d) with i = g2 + sum_j j*e_j + (d+1)*b in [0, m) (a superset of the
rows that actually occur) and cols by the monomials (a, b0, b_1..b_d) of the block with a < m.
Hence  rank <= sum_blocks min(#rows, #cols)  =: rank_bound, and

        dim Q > n * rank_bound   ==>   a nonzero interpolant exists.

hd_general_rank.py shows the true blocks are within ~1% of full rank, so this bound is nearly
tight; it needs no elimination and scales to m ~ 10^2-10^3 and d up to ~5.
"""
import math
import sys
import os
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hd_general_rank import _cap_iter, dim_space  # noqa: E402


def rank_bound(d, m, w, D, s, exact_rows=True):
    """sum over blocks of min(#rows, #cols).  With exact_rows=True the rows are the expansion
    keys that actually occur (no elimination is performed); with exact_rows=False a cheap
    combinatorial superset of the rows is used.  Both are sound upper bounds on the rank."""
    from hd_general_rank import multinomials
    blocks = {}
    for a in range(m):
        for bs in _cap_iter(d, s):
            wt = a + sum((w - 1 - j) * bs[j] for j in range(d))
            if wt >= D:
                continue
            b0max = (D - 1 - wt) // w
            g2 = a - sum((j + 1) * bs[j] for j in range(d))
            sb = sum(bs)
            for b0 in range(b0max + 1):
                key = (b0 + sb, g2)
                blocks.setdefault(key, []).append((a, b0, bs))
    total = 0
    for (g1, g2), bcols in blocks.items():
        nc = len(bcols)
        if exact_rows:
            rows = set()
            # rows of a column (a, b0, bs): keys (i, nE, e) over the multinomial expansion
            seen_b0 = {}
            for (a, b0, bs) in bcols:
                if b0 not in seen_b0:
                    seen_b0[b0] = [(ns, nE) for (ns, nE, _) in multinomials(b0, d)]
                for (ns, nE) in seen_b0[b0]:
                    i = a + sum((j + 1) * ns[j] for j in range(d)) + (d + 1) * nE
                    if i >= m:
                        continue
                    rows.add((i, nE, tuple(ns[j] + bs[j] for j in range(d))))
                    if len(rows) >= nc:
                        break
                if len(rows) >= nc:
                    break
            nr = len(rows)
        else:
            nr = 0
            def rec(j, rem, wsum):
                nonlocal nr
                if j == d:
                    i = g2 + wsum + (d + 1) * rem
                    if 0 <= i < m:
                        nr += 1
                    return
                for e in range(rem + 1):
                    rec(j + 1, rem - e, wsum + (j + 1) * e)
            rec(0, g1, 0)
        total += min(nr, nc)
    return total


def min_agreement_bound(d, n, k, m, s, lo=None, hi=None):
    w = k - 1
    lo = lo or k
    hi = hi or n

    def ok(A):
        D = m * A
        return dim_space(d, w, D, s) > n * rank_bound(d, m, w, D, s)
    if not ok(hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def omega_cap(s1, W, d):
    """TR26-164-style cap: b_1 <= s1, sum_{j>=2} (j-1) b_j <= W."""
    box = (s1,) + tuple(max(0, W // (j - 1)) for j in range(2, d + 1))
    pred = (lambda bs: sum((j - 1) * bs[j - 1] for j in range(2, d + 1)) <= W)
    return (box, pred)


def selftest():
    from hd_general_rank import node_rank, min_agreement
    n, k = 1 << 18, 1 << 17
    w = k - 1
    print("== bound >= exact rank, and bound-threshold >= exact threshold")
    fails = 0
    for (d, m, s) in [(1, 8, (2,)), (1, 12, (3,)), (2, 8, (2, 1)), (2, 12, (3, 2)),
                      (3, 12, omega_cap(3, 2, 3)), (3, 16, omega_cap(4, 3, 3))]:
        D = m * 184000
        rb = rank_bound(d, m, w, D, s)
        re_ = node_rank(d, m, w, D, s)
        Ab = min_agreement_bound(d, n, k, m, s, lo=170000)
        Ae = min_agreement(d, n, k, m, s, lo=170000)
        ok = rb >= re_ and Ab >= Ae
        fails += 0 if ok else 1
        print(f"  d={d} m={m}: bound={rb} exact={re_} (ratio {rb / re_:.4f});  A_bound={Ab} A_exact={Ae} "
              f"{'OK' if ok else 'VIOLATION'}")
    print("SELFTEST", "PASS" if fails == 0 else "FAIL")
    return fails


if __name__ == "__main__":
    sys.exit(1 if selftest() else 0)
