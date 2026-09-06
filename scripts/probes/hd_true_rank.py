#!/usr/bin/env python3
"""
hd_true_rank.py — the TRUE per-node constraint rank for hidden-derivative interpolation.

TR26-164 / PR #122 impose, at a node (alpha, y), vanishing of every coefficient of
T^i E^b Y^e (i + d*b < m) in Q(alpha+T, y + sum_j (-1)^{j+1} T^j Y_j + T E, Y_1..Y_d) with
Y_j, E treated as independent formal constants.  That is a SUFFICIENT system.  The genuine
requirement is only

    Q(alpha+T, f(T), f^{[1]}(T), ..., f^{[d]}(T)) = 0  (mod T^m)   for every f with f(0) = y,

where f^{[j]} is the j-th Hasse derivative of f = P(alpha + T).  Writing f = y + T*U with
U = sum_l u_l T^l (u_l free), this is a polynomial identity in u_0, ..., u_{m-1+d}; its
coefficients are linear functionals on Q.  The rank of that system is the exact number of
linear conditions the node imposes — never larger than the formal count, and (as this probe
shows) strictly smaller.

The probe computes this true rank by direct expansion for small (m, s) in the LD setting
(and the line setting with node (y0,y1) = (0,1)), compares with the formal rank of
hd1_interpolation_threshold / hd_general_rank, and rescans the least-agreement threshold.
"""
import math
import sys
import os
from functools import lru_cache
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hd1_interpolation_threshold import ld_rank_formula, ld_dim, line_dim, line_rank_blocks  # noqa
from hd_general_rank import node_rank, dim_space, rank_mod_p  # noqa

P = 2_147_483_647


# ---- multivariate polynomial (in u's) coefficients of T-series mod T^m ------------------
# A "series" is a list of length m; entry i is a dict {monomial: coeff}, monomial = tuple of
# (var_index, exponent) pairs sorted, coefficients mod P.

def s_zero(m):
    return [dict() for _ in range(m)]


def s_const(c, m):
    s = s_zero(m)
    s[0][()] = c % P
    return s


def mono_mul(m1, m2):
    d = dict(m1)
    for v, e in m2:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def s_mul(a, b, m):
    out = s_zero(m)
    for i, da in enumerate(a):
        if not da:
            continue
        for j, db in enumerate(b):
            if i + j >= m:
                break
            if not db:
                continue
            tgt = out[i + j]
            for ma, ca in da.items():
                for mb, cb in db.items():
                    mm = mono_mul(ma, mb)
                    tgt[mm] = (tgt.get(mm, 0) + ca * cb) % P
    return out


def s_pow(a, e, m):
    r = s_const(1, m)
    base = a
    while e:
        if e & 1:
            r = s_mul(r, base, m)
        base = s_mul(base, base, m)
        e >>= 1
    return r


def s_add(a, b, m):
    out = s_zero(m)
    for i in range(m):
        d = dict(a[i])
        for k, v in b[i].items():
            d[k] = (d.get(k, 0) + v) % P
        out[i] = {k: v for k, v in d.items() if v}
    return out


def s_scale(a, c, m):
    return [{k: (v * c) % P for k, v in d.items()} for d in a]


def hasse(series, j, m):
    """j-th Hasse derivative of a series in T (mod T^m; input given mod T^{m+j} ideally)."""
    out = s_zero(m)
    for l in range(m):
        src = l + j
        if src < len(series):
            c = math.comb(src, j) % P
            if c:
                out[l] = {k: (v * c) % P for k, v in series[src].items()}
    return out


def build_true_matrix(d, m, w, D, s, L=None, line=False):
    """Rows = coefficients (i, u-monomial, [Z-degree]) of Q(alpha+T, f, f^[1..d], [Z]) mod T^m,
    node (0,0) [line: (y0,y1)=(0,1)], over columns (a<m, b0, b1..bd, [l0])."""
    mm = m + d  # need f up to T^{m+d-1} for the d-th Hasse derivative mod T^m
    # f = T*U, U = sum_{l} u_l T^l, l = 0..mm-2   (variables u_0 .. u_{mm-2})
    f = s_zero(mm)
    for l in range(mm - 1):
        f[l + 1] = {((l, 1),): 1}
    # line: f = Z + T*U ; Z is variable index 'Z' -> encode as var index -1
    if line:
        f[0] = {((-1, 1),): 1}
    derivs = [f[:m]] + [hasse(f, j, m) for j in range(1, d + 1)]
    # precompute powers lazily
    pow_cache = {}

    def spow(idx, e):
        key = (idx, e)
        if key not in pow_cache:
            pow_cache[key] = s_pow(derivs[idx], e, m)
        return pow_cache[key]
    T = s_zero(m)
    if m > 1:
        T[1] = {(): 1}
    Tpow = {0: s_const(1, m)}
    for e in range(1, m):
        Tpow[e] = s_mul(Tpow[e - 1], T, m)
    Z = s_zero(m)
    Z[0] = {((-1, 1),): 1}
    Zpow = {0: s_const(1, m)}

    s = list(s)
    cols = []
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
    rows = {}
    for ci, (a, b0, bs, l0) in enumerate(cols):
        term = Tpow[a]
        term = s_mul(term, spow(0, b0), m)
        for j in range(d):
            if bs[j]:
                term = s_mul(term, spow(j + 1, bs[j]), m)
        if line and l0:
            if l0 not in Zpow:
                Zpow[l0] = s_pow(Z, l0, m)
            term = s_mul(term, Zpow[l0], m)
        for i in range(m):
            for mono, c in term[i].items():
                key = (i, mono)
                rows.setdefault(key, {})[ci] = c
    keys = list(rows)
    M = np.zeros((len(keys), len(cols)), dtype=np.int64)
    for ri, kk in enumerate(keys):
        for ci, v in rows[kk].items():
            M[ri, ci] = v
    return M, len(keys), len(cols)


def true_rank(d, m, w, D, s, L=None, line=False):
    M, nr, nc = build_true_matrix(d, m, w, D, s, L, line)
    return rank_mod_p(M), nr, nc


def main():
    n, k = 1 << 18, 1 << 17
    w = k - 1
    print("== d=0 sanity (GS): true rank must equal m(m+1)/2")
    for m in [3, 4, 5, 6]:
        r, nr, nc = true_rank(0, m, w, m * 186000, ())
        print(f"  m={m}: true={r} GS={m * (m + 1) // 2} {'OK' if r == m * (m + 1) // 2 else 'DIFF'}")

    print("== d=1 LD: true rank vs formal (TR26-164/nasqret) rank")
    for (m, s) in [(3, 1), (4, 1), (4, 2), (5, 1), (5, 2), (6, 2), (6, 3), (7, 2), (8, 2), (8, 3), (9, 3), (10, 3)]:
        D = m * 186000
        r_true, nr, nc = true_rank(1, m, w, D, (s,))
        r_formal = ld_rank_formula(D, w, s, m)
        print(f"  m={m} s={s}: true={r_true} formal={r_formal} cols(a<m)={nc} rows={nr}  "
              f"ratio true/formal={r_true / r_formal:.3f}", flush=True)

    print("== d=2 LD: true rank vs formal rank")
    for (m, s) in [(4, (1, 1)), (5, (2, 1)), (6, (2, 1)), (6, (2, 2)), (8, (2, 1)), (8, (3, 2))]:
        D = m * 186000
        r_true, nr, nc = true_rank(2, m, w, D, s)
        r_formal = node_rank(2, m, w, D, s)
        print(f"  m={m} s={s}: true={r_true} formal={r_formal} cols(a<m)={nc}  "
              f"ratio={r_true / r_formal:.3f}", flush=True)

    print("== d=1 LINE: true rank vs formal rank")
    for (m, s, L) in [(3, 1, 3), (4, 1, 4), (4, 2, 4), (5, 2, 6), (6, 2, 6)]:
        D = m * 186000
        r_true, nr, nc = true_rank(1, m, w, D, (s,), L, line=True)
        r_formal, _, _ = line_rank_blocks(D, w, s, L, m)
        print(f"  m={m} s={s} L={L}: true={r_true} formal={r_formal} cols={nc} ratio={r_true / r_formal:.3f}",
              flush=True)


if __name__ == "__main__":
    main()
