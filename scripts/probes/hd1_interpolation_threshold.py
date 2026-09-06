#!/usr/bin/env python3
"""
hd1_interpolation_threshold.py — exact interpolation thresholds for the d=1
hidden-derivative ("contact") interpolant, in the list-decoding (LD) setting and in the
affine-line (MCA) setting.

Background.  ECCC TR26-164 (Brakensiek–Chen–Putterman–Zhang–Zheng, 2026-09-04) and the
better.codes PR #122 (nasqret, 2026-08-27) interpolate a polynomial Q(X, Y0, Y1) (LD) or
Q(X, Y, R, Z) (line) in which Y1 / R is a *hidden* first Hasse derivative of the unknown
message polynomial.  At a received node (alpha, y) the constraint is: writing
X = alpha + T, Y0 = y + T*Y1 + T*E (E = remainder, divisible by T for genuine P), every
coefficient of T^i E^b (i + b < m) in the substituted Q vanishes.  Lemma 3.1 of TR26-164
then gives multiplicity >= m at alpha for Q(X, P, P') whenever P(alpha) = y.

This probe computes, EXACTLY,
  * the dimension of the interpolation space Q for given (n, k, A, m, s, L),
  * the rank of the per-node constraint map Phi (by block decomposition, cross-checked
    against brute-force modular Gaussian elimination at small sizes),
  * the least agreement A with dim Q > n * rank(Phi)  (existence of a nonzero interpolant),
and scans (m, s, L) at rate 1/2 to see how far beyond the Johnson agreement sqrt(n(k-1)) the
d=1 interpolation threshold moves.  It also checks the contact constraint semantically on
random instances over F_p (Q in kernel  =>  Q(alpha+T, P(alpha+T), P'(alpha+T)) = 0 mod T^m).

Nothing here is a list-size / bad-seed count; that is the separate Bezout-type ledger.
Run:  python3 scripts/probes/hd1_interpolation_threshold.py [--quick]
"""
import argparse
import math
import random
import sys
from functools import lru_cache

import numpy as np

P = 2_147_483_647  # 2^31 - 1, prime; products fit in int64


# ----------------------------------------------------------------------------------------
# modular linear algebra (dense, small)
# ----------------------------------------------------------------------------------------
def rank_mod_p(M):
    """Rank of an integer matrix (list of rows or np.array) over F_P."""
    A = np.array(M, dtype=np.int64) % P
    if A.size == 0:
        return 0
    nrows, ncols = A.shape
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        piv = None
        for i in range(r, nrows):
            if A[i, c] != 0:
                piv = i
                break
        if piv is None:
            continue
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
def binom(n, k):
    if k < 0 or k > n or n < 0:
        return 0
    return math.comb(n, k)


# ----------------------------------------------------------------------------------------
# LD setting:  Q(X, Y0, Y1),  monomials X^a Y0^b0 Y1^b1,  b1 <= s,  a + w*b0 + (w-1)*b1 < D
#   (w = k-1 = max degree of P; weights (1, w, w-1) as in TR26-164 with d = 1).
#   Node (alpha, y) = (0, 0):  Q(T, T*(Y1+E), Y1);  rows (i, b, e): coeff of T^i E^b Y1^e,
#   i + b < m.
# ----------------------------------------------------------------------------------------
def ld_dim(D, w, s):
    """#{(a,b0,b1): b1<=s, a + w*b0 + (w-1)*b1 < D}."""
    tot = 0
    for b1 in range(s + 1):
        rem = D - (w - 1) * b1
        if rem <= 0:
            break
        # sum over b0 >= 0 of max(0, rem - w*b0)
        b0max = (rem - 1) // w
        # sum_{b0=0}^{b0max} (rem - w b0)
        tot += (b0max + 1) * rem - w * b0max * (b0max + 1) // 2
    return tot


def ld_rank_formula(D, w, s, m):
    """Exact rank of the node map via block decomposition.
    Column (a,b0,b1) with a<m lands in block (i,j) = (a+b0, b0+b1); row (i,b,e) in block
    (i, e+b).  Block (i,j): rows b in [0, min(m-1-i, j)], columns b0 in
    [max(0,j-s), min(i,j)] subject to a=i-b0 and the degree budget; entries C(b0,b) ->
    full rank min(#rows,#cols)."""
    rank = 0
    for i in range(m):
        # j ranges: b0+b1 with b0<=i, b1<=s  -> j <= i+s
        for j in range(0, i + s + 1):
            nrows = min(m - 1 - i, j) + 1
            ncols = 0
            for b0 in range(max(0, j - s), min(i, j) + 1):
                a = i - b0
                b1 = j - b0
                if a + w * b0 + (w - 1) * b1 < D:
                    ncols += 1
            rank += min(nrows, ncols)
    return rank


def ld_rank_bruteforce(D, w, s, m):
    cols = [(a, b0, b1) for a in range(m) for b1 in range(s + 1)
            for b0 in range(0, (D - a - (w - 1) * b1 - 1) // w + 1)
            if a + w * b0 + (w - 1) * b1 < D]
    rows = {}
    for ci, (a, b0, b1) in enumerate(cols):
        for b in range(0, b0 + 1):
            i = a + b0
            if i + b >= m:
                continue
            e = b0 - b + b1
            key = (i, b, e)
            rows.setdefault(key, {})[ci] = binom(b0, b)
    keys = list(rows)
    M = np.zeros((len(keys), len(cols)), dtype=np.int64)
    for ri, key in enumerate(keys):
        for ci, v in rows[key].items():
            M[ri, ci] = v % P
    return rank_mod_p(M), len(keys), len(cols)


def ld_min_agreement(n, k, m, s, A_lo=None, A_hi=None):
    """Least A with dim Q > n * rank(Phi).  D = m*A."""
    w = k - 1
    lo = A_lo or (k)
    hi = A_hi or n
    # monotone in A (dim grows faster than rank); binary search for first A satisfying
    def ok(A):
        D = m * A
        return ld_dim(D, w, s) > n * ld_rank_formula(D, w, s, m)
    if not ok(hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


# ----------------------------------------------------------------------------------------
# semantic check of the contact constraint (Lemma 3.1 of TR26-164, d = 1)
# ----------------------------------------------------------------------------------------
def poly_mul_mod(a, b, mdeg):
    out = [0] * min(len(a) + len(b) - 1, mdeg)
    for i, x in enumerate(a):
        if x == 0 or i >= mdeg:
            continue
        for j, y in enumerate(b):
            if i + j >= mdeg:
                break
            out[i + j] = (out[i + j] + x * y) % P
    return out


def poly_add(a, b):
    n = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % P for i in range(n)]


def poly_pow_mod(a, e, mdeg):
    r = [1]
    base = a[:mdeg]
    while e:
        if e & 1:
            r = poly_mul_mod(r, base, mdeg)
        base = poly_mul_mod(base, base, mdeg)
        e >>= 1
    return r


def semantic_check(w, s, m, D, trials=3, seed=1):
    """Sample Q in ker(Phi at node (alpha,y)) and P through (alpha,y); check multiplicity."""
    rng = random.Random(seed)
    alpha, y = rng.randrange(P), rng.randrange(P)
    # Build Phi at (alpha, y) explicitly: substitute X = alpha+T, Y0 = y + T*Y1 + T*E.
    # monomial X^a Y0^b0 Y1^b1 -> sum_{t<=a} C(a,t) alpha^{a-t} T^t * sum_{c<=b0} C(b0,c)
    #   y^{b0-c} T^c (Y1+E)^c Y1^{b1} ; (Y1+E)^c = sum_b C(c,b) E^b Y1^{c-b}.
    cols = [(a, b0, b1) for a in range(D) for b1 in range(s + 1)
            for b0 in range(0, (D - a - (w - 1) * b1 - 1) // w + 1)
            if a + w * b0 + (w - 1) * b1 < D]
    rows = {}
    for ci, (a, b0, b1) in enumerate(cols):
        for t in range(0, min(a, m - 1) + 1):
            ca = binom(a, t) * pow(alpha, a - t, P) % P
            for c in range(0, b0 + 1):
                i = t + c
                if i >= m:
                    break
                cb = binom(b0, c) * pow(y, b0 - c, P) % P
                for b in range(0, c + 1):
                    if i + b >= m:
                        break
                    e = c - b + b1
                    key = (i, b, e)
                    v = ca * cb % P * binom(c, b) % P
                    rows.setdefault(key, {})
                    rows[key][ci] = (rows[key].get(ci, 0) + v) % P
    keys = list(rows)
    M = np.zeros((len(keys), len(cols)), dtype=np.int64)
    for ri, key in enumerate(keys):
        for ci, v in rows[key].items():
            M[ri, ci] = v
    # nullspace vector via elimination (find a kernel element): reduce and pick free column
    A = M.copy() % P
    nrows, ncols = A.shape
    pivcols = []
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        piv = None
        for i2 in range(r, nrows):
            if A[i2, c] != 0:
                piv = i2
                break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        nz = np.nonzero(col)[0]
        if len(nz):
            A[nz] = (A[nz] - (col[nz][:, None] * A[r][None, :]) % P) % P
        pivcols.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in set(pivcols)]
    assert free, "no free column: constraint map injective at these sizes"
    results = []
    for _ in range(trials):
        f = rng.choice(free)
        vec = [0] * ncols
        vec[f] = 1
        for ri2, pc in enumerate(pivcols):
            vec[pc] = (-int(A[ri2, f])) % P
        # random P of degree <= w with P(alpha) = y
        coeffs = [rng.randrange(P) for _ in range(w + 1)]
        val = sum(cf * pow(alpha, i2, P) for i2, cf in enumerate(coeffs)) % P
        coeffs[0] = (coeffs[0] - val + y) % P
        # P(alpha+T), P'(alpha+T) as series in T mod T^m
        PT = [0] * m
        for i2, cf in enumerate(coeffs):
            for t in range(0, min(i2, m - 1) + 1):
                PT[t] = (PT[t] + cf * binom(i2, t) * pow(alpha, i2 - t, P)) % P
        dcoeffs = [(i2 * coeffs[i2]) % P for i2 in range(1, w + 1)]
        DT = [0] * m
        for i2, cf in enumerate(dcoeffs):
            for t in range(0, min(i2, m - 1) + 1):
                DT[t] = (DT[t] + cf * binom(i2, t) * pow(alpha, i2 - t, P)) % P
        XT = [alpha % P, 1] + [0] * (m - 2)
        total = [0] * m
        for ci, (a, b0, b1) in enumerate(cols):
            if vec[ci] == 0:
                continue
            term = [vec[ci]]
            term = poly_mul_mod(term, poly_pow_mod(XT, a, m), m)
            term = poly_mul_mod(term, poly_pow_mod(PT, b0, m), m)
            term = poly_mul_mod(term, poly_pow_mod(DT, b1, m), m)
            total = poly_add(total, term)
        results.append(all(t == 0 for t in total[:m]))
    return results


# ----------------------------------------------------------------------------------------
# Line / MCA setting:  Q(X, Y, R, Z), monomials X^a Y^b0 R^b1 Z^l0, b0 + l0 <= L, b1 <= s,
#   a + w*b0 + (w-1)*b1 < D.  Node with (y0, y1) = (0, 1):  Q(T, Z + T*(Y1+E), Y1, Z);
#   rows (i, b, e, l) with i + b < m.  Blocks (g1, g2) = (a+b0+l0, b1-a) = (i+l, e+b-i).
# ----------------------------------------------------------------------------------------
def line_dim(D, w, s, L):
    tot = 0
    for b1 in range(s + 1):
        rem = D - (w - 1) * b1
        if rem <= 0:
            break
        b0max = min((rem - 1) // w, L)
        for b0 in range(b0max + 1):
            tot += (rem - w * b0) * (L - b0 + 1)
    return tot


def line_rank_blocks(D, w, s, L, m, y1_nonzero=True):
    """Exact rank of the per-node map for (y0,y1)=(0,1) [or (0,0) if y1_nonzero=False]
    by block elimination mod P.  Returns (rank, #rows_total, #cols_total)."""
    rank = 0
    rows_total = 0
    cols_total = 0
    if not y1_nonzero:
        # Y = T*(Y1+E): Z-degree of monomial passes through untouched -> same as LD rank
        # times nothing (each l0 separately): rank = sum over l0 of LD-rank with column
        # budget b0 <= L - l0.
        for l0 in range(L + 1):
            Lb = L - l0
            for i in range(m):
                for j in range(0, i + s + 1):
                    nrows = min(m - 1 - i, j) + 1
                    ncols = 0
                    for b0 in range(max(0, j - s), min(i, j, Lb) + 1):
                        a = i - b0
                        b1 = j - b0
                        if a + w * b0 + (w - 1) * b1 < D:
                            ncols += 1
                    rank += min(nrows, ncols)
        return rank, None, None
    # y1 != 0: blocks (g1, g2)
    for g1 in range(0, L + m):
        for g2 in range(-(m - 1), s + 1):
            cols = []
            for a in range(m):
                b1 = g2 + a
                if b1 < 0 or b1 > s:
                    continue
                for b0 in range(0, g1 - a + 1):
                    l0 = g1 - a - b0
                    if l0 < 0 or b0 + l0 > L:
                        continue
                    if a + w * b0 + (w - 1) * b1 < D:
                        cols.append((a, b0))
            if not cols:
                continue
            rows = []
            for i in range(m):
                l = g1 - i
                if l < 0:
                    continue
                for b in range(0, m - i):
                    e = g2 + i - b
                    if e < 0:
                        continue
                    rows.append((i, b))
            if not rows:
                continue
            M = np.zeros((len(rows), len(cols)), dtype=np.int64)
            for ri, (i, b) in enumerate(rows):
                for ci, (a, b0) in enumerate(cols):
                    c = i - a
                    if c < 0 or c > b0 or b > c:
                        continue
                    M[ri, ci] = (binom(b0, c) * binom(c, b)) % P
            rows_total += len(rows)
            cols_total += len(cols)
            rank += rank_mod_p(M)
    return rank, rows_total, cols_total


def line_rank_bruteforce(D, w, s, L, m):
    cols = [(a, b0, b1, l0) for a in range(m) for b1 in range(s + 1)
            for b0 in range(0, L + 1) for l0 in range(0, L - b0 + 1)
            if a + w * b0 + (w - 1) * b1 < D]
    rows = {}
    for ci, (a, b0, b1, l0) in enumerate(cols):
        for c in range(0, b0 + 1):
            i = a + c
            if i >= m:
                break
            for b in range(0, c + 1):
                if i + b >= m:
                    break
                e = c - b + b1
                l = b0 - c + l0
                key = (i, b, e, l)
                rows.setdefault(key, {})
                rows[key][ci] = (rows[key].get(ci, 0) + binom(b0, c) * binom(c, b)) % P
    keys = list(rows)
    M = np.zeros((len(keys), len(cols)), dtype=np.int64)
    for ri, key in enumerate(keys):
        for ci, v in rows[key].items():
            M[ri, ci] = v
    return rank_mod_p(M), len(keys), len(cols)


def line_min_agreement(n, k, m, s, L, A_lo=None, A_hi=None, cache=None):
    w = k - 1
    lo = A_lo or k
    hi = A_hi or n

    def ok(A):
        D = m * A
        r, _, _ = line_rank_blocks(D, w, s, L, m)
        return line_dim(D, w, s, L) > n * r
    if not ok(hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


# ----------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    fails = 0

    print("== A. LD d=1: brute-force rank vs block formula (small parameters)")
    for (w, s, m, D) in [(5, 1, 3, 40), (7, 2, 4, 70), (6, 3, 5, 90), (9, 2, 6, 120),
                         (11, 4, 7, 200)]:
        rb, nr, nc = ld_rank_bruteforce(D, w, s, m)
        rf = ld_rank_formula(D, w, s, m)
        ok = rb == rf
        fails += 0 if ok else 1
        print(f"  w={w} s={s} m={m} D={D}: brute rank={rb} (rows={nr}, cols(a<m)={nc}) "
              f"formula={rf} {'OK' if ok else 'MISMATCH'}")

    print("== B. semantic contact check (Q in ker Phi(alpha,y) => mult >= m for P through node)")
    for (w, s, m, D) in [(4, 1, 3, 30), (5, 2, 4, 50), (6, 2, 5, 70)]:
        res = semantic_check(w, s, m, D, trials=3, seed=w * 7 + m)
        ok = all(res)
        fails += 0 if ok else 1
        print(f"  w={w} s={s} m={m} D={D}: {res} {'OK' if ok else 'FAIL'}")

    print("== C. line d=1: brute-force rank vs block elimination (small parameters)")
    for (w, s, L, m, D) in [(5, 1, 3, 3, 40), (6, 2, 4, 4, 70), (7, 1, 5, 5, 90),
                            (8, 2, 6, 5, 120)]:
        rb, nr, nc = line_rank_bruteforce(D, w, s, L, m)
        rf, _, _ = line_rank_blocks(D, w, s, L, m)
        ok = rb == rf
        fails += 0 if ok else 1
        print(f"  w={w} s={s} L={L} m={m} D={D}: brute rank={rb} (rows={nr}, cols={nc}) "
              f"blocks={rf} {'OK' if ok else 'MISMATCH'}")

    print("== D. reproduce nasqret PR#122 dimension: n=2^18, w=131071, m=13, L=169, s=3, a=185354")
    n, w, m, L, s, a = 1 << 18, 131071, 13, 169, 3, 185354
    D = m * a
    dimQ = line_dim(D, w, s, L)
    print(f"  dim Q = {dimQ}  (PR states 13096794720)  {'OK' if dimQ == 13096794720 else 'DIFF'}")
    if not args.quick:
        r, rt, ct = line_rank_blocks(D, w, s, L, m)
        print(f"  exact per-node rank (y1!=0) = {r}   n*rank = {n * r}   "
              f"(PR bound 49960/node, n*49960 = {n * 49960})  dimQ > n*rank: {dimQ > n * r}")

    print("== E. LD d=1 threshold scan at rate 1/2 (n = 2^18, k = 2^17): least A with dim Q > n*rank")
    n, k = 1 << 18, 1 << 17
    AJ = math.isqrt(n * (k - 1)) + 1
    print(f"  Johnson/GS agreement floor: A_J = ceil(sqrt(n(k-1))) = {AJ}, delta_J = {1 - AJ / n:.5f}")
    grid = [(3, 1), (5, 1), (5, 2), (8, 2), (8, 4), (12, 3), (12, 6), (16, 8), (24, 12),
            (32, 16), (48, 24), (64, 32)]
    if args.quick:
        grid = grid[:6]
    for (m, s) in grid:
        A = ld_min_agreement(n, k, m, s)
        print(f"  m={m:3d} s={s:3d}: A_min={A}  delta={1 - A / n:.5f}  "
              f"beyond-Johnson positions={AJ - A}  A/sqrt(n(k-1))={A / math.sqrt(n * (k - 1)):.5f}")

    print("== F. line d=1 threshold scan at rate 1/2 (n = 2^18, k = 2^17)")
    grid2 = [(3, 1, 20), (5, 2, 40), (8, 2, 60), (8, 4, 80), (13, 3, 169), (12, 6, 120)]
    if args.quick:
        grid2 = grid2[:3]
    for (m, s, L) in grid2:
        A = line_min_agreement(n, k, m, s, L)
        print(f"  m={m:3d} s={s:3d} L={L:4d}: A_min={A}  delta={1 - A / n:.5f}  "
              f"beyond-Johnson positions={AJ - A}")

    print(f"\nSUMMARY: {'PASS' if fails == 0 else 'FAIL'} ({fails} check failures)")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
