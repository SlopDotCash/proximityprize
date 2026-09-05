#!/usr/bin/env python3
"""
hd_general_rank.py — exact per-node constraint rank and interpolation threshold for the
order-d hidden-derivative interpolant of ECCC TR26-164, in the list-decoding (LD) and
affine-line (LINE) settings, for any d >= 1.

Interpolant monomials (LD):   X^a Y0^b0 Y1^b1 ... Yd^bd,  b_j <= s_j (j>=1),
                              a + w*b0 + (w-1)*b1 + ... + (w-d)*bd < D.
Interpolant monomials (LINE): additionally Z^l0 with b0 + l0 <= L.
Node substitution (TR26-164 eq. (25), node (alpha,y) -> (0,0) by translation; LINE node
(y0,y1) -> (0,1) by translation/scaling when y1 != 0):
    X = T,   Y0 = [Z] + sum_{j=1}^d (-1)^{j+1} T^j Y_j + T^{d+1} E.
Constraint: every coefficient of T^i (i < m), any E / Y_j / Z degrees, vanishes.

Rank is computed by exact modular elimination inside the invariant blocks
    g1 = b0 + sum_j b_j (+ l0),      g2 = a - sum_j j*b_j,
which the substitution preserves (rows: g1 = sum_j e_j + b (+ l), g2 = i - sum_j j e_j - (d+1) b).

Cross-checked against hd1_interpolation_threshold.py for d = 1.
"""
import math
import sys
from functools import lru_cache
from itertools import product

import numpy as np

P = 2_147_483_647


@lru_cache(maxsize=None)
def binom(n, k):
    if k < 0 or k > n:
        return 0
    return math.comb(n, k)


def rank_mod_p(M):
    A = np.array(M, dtype=np.int64) % P
    if A.size == 0:
        return 0
    nrows, ncols = A.shape
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        nzs = np.nonzero(A[r:, c])[0]
        if len(nzs) == 0:
            continue
        piv = r + nzs[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        nz = np.nonzero(col)[0]
        if len(nz):
            A[nz] = (A[nz] - (col[nz][:, None] * A[r][None, :]) % P) % P
        r += 1
    return r


@lru_cache(maxsize=None)
def multinomials(b0, d):
    """All (n_1..n_d, n_E) with sum = b0, with multinomial coefficient b0!/(prod n_j! n_E!)."""
    out = []
    def rec(rem, idx, cur):
        if idx == d:
            nE = rem
            coef = math.factorial(b0)
            for x in cur:
                coef //= math.factorial(x)
            coef //= math.factorial(nE)
            out.append((tuple(cur), nE, coef))
            return
        for x in range(rem + 1):
            rec(rem - x, idx + 1, cur + [x])
    rec(b0, 0, [])
    return out


def columns(d, m, w, D, s, L=None):
    """Enumerate columns with a < m (others are killed by T^m at the node)."""
    cols = []
    s = list(s)
    ranges = [range(s[j] + 1) for j in range(d)]
    for a in range(m):
        for bs in product(*ranges):
            wt = a + sum((w - 1 - j) * bs[j] for j in range(d))
            if wt >= D:
                continue
            b0max = (D - 1 - wt) // w
            if L is not None:
                b0max = min(b0max, L)
            for b0 in range(b0max + 1):
                if L is None:
                    cols.append((a, b0, bs, 0))
                else:
                    for l0 in range(L - b0 + 1):
                        cols.append((a, b0, bs, l0))
    return cols


def node_rank(d, m, w, D, s, L=None, y1_nonzero=True, return_blocks=False):
    """Exact rank of the per-node constraint map."""
    cols = columns(d, m, w, D, s, L)
    blocks = {}
    for col in cols:
        a, b0, bs, l0 = col
        g1 = b0 + sum(bs) + l0
        g2 = a - sum((j + 1) * bs[j] for j in range(d))
        blocks.setdefault((g1, g2), []).append(col)
    total = 0
    nblocks = 0
    for key, bcols in blocks.items():
        rows = {}
        for ci, (a, b0, bs, l0) in enumerate(bcols):
            # expansion of Y0^b0 where Y0 = [Z] + sum_j c_j T^j Y_j + T^{d+1} E
            if L is not None and y1_nonzero:
                # choose nZ factors of Z among b0, rest from derivative/E terms
                for nZ in range(b0 + 1):
                    cz = binom(b0, nZ)
                    for (ns, nE, coef) in multinomials(b0 - nZ, d):
                        i = a + sum((j + 1) * ns[j] for j in range(d)) + (d + 1) * nE
                        if i >= m:
                            continue
                        sign = 1
                        for j in range(d):
                            if (j % 2 == 1) and (ns[j] % 2 == 1):  # (-1)^{j+1} with j index 0-based: Y_{j+1} gets (-1)^{j+2} = (-1)^j
                                pass
                        # sign of prod_j ((-1)^{(j+1)+1})^{n_j} = prod_j (-1)^{j n_j} (0-based j)
                        for j in range(d):
                            if (j * ns[j]) % 2 == 1:
                                sign = -sign
                        e = tuple(ns[j] + bs[j] for j in range(d))
                        l = nZ + l0
                        key2 = (i, nE, e, l)
                        rows.setdefault(key2, {})
                        rows[key2][ci] = (rows[key2].get(ci, 0) + sign * cz * coef) % P
            else:
                for (ns, nE, coef) in multinomials(b0, d):
                    i = a + sum((j + 1) * ns[j] for j in range(d)) + (d + 1) * nE
                    if i >= m:
                        continue
                    sign = 1
                    for j in range(d):
                        if (j * ns[j]) % 2 == 1:
                            sign = -sign
                    e = tuple(ns[j] + bs[j] for j in range(d))
                    key2 = (i, nE, e, l0)
                    rows.setdefault(key2, {})
                    rows[key2][ci] = (rows[key2].get(ci, 0) + sign * coef) % P
        if not rows:
            continue
        keys = list(rows)
        M = np.zeros((len(keys), len(bcols)), dtype=np.int64)
        for ri, kk in enumerate(keys):
            for ci, v in rows[kk].items():
                M[ri, ci] = v
        total += rank_mod_p(M)
        nblocks += 1
    if return_blocks:
        return total, nblocks, len(cols)
    return total


def dim_space(d, w, D, s, L=None):
    """Exact dimension of the interpolation space (all a >= 0)."""
    s = list(s)
    ranges = [range(s[j] + 1) for j in range(d)]
    tot = 0
    for bs in product(*ranges):
        wt = sum((w - 1 - j) * bs[j] for j in range(d))
        rem = D - wt
        if rem <= 0:
            continue
        b0max = (rem - 1) // w
        if L is not None:
            b0max = min(b0max, L)
        for b0 in range(b0max + 1):
            cnt_a = rem - w * b0
            if L is None:
                tot += cnt_a
            else:
                tot += cnt_a * (L - b0 + 1)
    return tot


def min_agreement(d, n, k, m, s, L=None, lo=None, hi=None, verbose=False):
    w = k - 1
    lo = lo or k
    hi = hi or n

    def ok(A):
        D = m * A
        r = node_rank(d, m, w, D, s, L)
        dq = dim_space(d, w, D, s, L)
        if verbose:
            print(f"    A={A}: dim={dq} rank/node={r} n*rank={n * r} ok={dq > n * r}", flush=True)
        return dq > n * r
    if not ok(hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def selftest():
    sys.path.insert(0, "scripts/probes")
    from hd1_interpolation_threshold import (ld_rank_formula, ld_dim, line_rank_blocks,
                                             line_dim)
    fails = 0
    print("== d=1 LD cross-check")
    for (w, s, m, D) in [(5, 1, 3, 40), (7, 2, 4, 70), (6, 3, 5, 90), (11, 4, 7, 200)]:
        r1 = ld_rank_formula(D, w, s, m)
        r2 = node_rank(1, m, w, D, (s,))
        d1 = ld_dim(D, w, s)
        d2 = dim_space(1, w, D, (s,))
        ok = (r1 == r2) and (d1 == d2)
        fails += 0 if ok else 1
        print(f"  w={w} s={s} m={m} D={D}: rank {r1} vs {r2}, dim {d1} vs {d2} {'OK' if ok else 'MISMATCH'}")
    print("== d=1 LINE cross-check")
    for (w, s, L, m, D) in [(5, 1, 3, 3, 40), (6, 2, 4, 4, 70), (8, 2, 6, 5, 120)]:
        r1, _, _ = line_rank_blocks(D, w, s, L, m)
        r2 = node_rank(1, m, w, D, (s,), L)
        d1 = line_dim(D, w, s, L)
        d2 = dim_space(1, w, D, (s,), L)
        ok = (r1 == r2) and (d1 == d2)
        fails += 0 if ok else 1
        print(f"  w={w} s={s} L={L} m={m} D={D}: rank {r1} vs {r2}, dim {d1} vs {d2} {'OK' if ok else 'MISMATCH'}")
    print("== d=2 LD small: rank vs full brute force (no blocks)")
    for (w, s, m, D) in [(6, (1, 1), 3, 40), (8, (2, 1), 4, 70), (9, (2, 2), 5, 100)]:
        r2 = node_rank(2, m, w, D, s)
        # brute: build the full matrix ignoring blocks
        cols = columns(2, m, w, D, s)
        rows = {}
        for ci, (a, b0, bs, l0) in enumerate(cols):
            for (ns, nE, coef) in multinomials(b0, 2):
                i = a + ns[0] + 2 * ns[1] + 3 * nE
                if i >= m:
                    continue
                sign = -1 if (ns[1] % 2 == 1) else 1
                key = (i, nE, ns[0] + bs[0], ns[1] + bs[1])
                rows.setdefault(key, {})
                rows[key][ci] = (rows[key].get(ci, 0) + sign * coef) % P
        keys = list(rows)
        M = np.zeros((len(keys), len(cols)), dtype=np.int64)
        for ri, kk in enumerate(keys):
            for ci, v in rows[kk].items():
                M[ri, ci] = v
        rb = rank_mod_p(M)
        ok = rb == r2
        fails += 0 if ok else 1
        print(f"  w={w} s={s} m={m} D={D}: blocks {r2} vs brute {rb} {'OK' if ok else 'MISMATCH'}")
    print(f"SELFTEST {'PASS' if fails == 0 else 'FAIL'}")
    return fails


if __name__ == "__main__":
    sys.exit(1 if selftest() else 0)
