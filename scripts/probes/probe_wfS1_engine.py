# probe_wfS1_engine.py
# High-performance int64-vectorized engine for CRACK D list-growth (issue #444).
#
# All primes here satisfy p^2 < 2^63, so modular multiply (a*b) % p is exact in
# int64 numpy -- fully vectorized, ~100-1000x faster than python-int per-element.
#
# Provides:
#   FieldE: field/subgroup with int64 power table P[i,e] = pts[i]^e mod p.
#   batch interpolation of MANY k-subsets at once (vectorized Gaussian elim mod p).
#   exact list count for a word (enumerate k-subsets in batches).
#   lacunary lower-bound count (vectorized over a codeword pool matrix).

import sys, os, math
sys.path.insert(0, os.path.dirname(__file__))
from probe_wfS1_core import PRIMES, validate, subgroup
import numpy as np
from itertools import combinations
from math import comb

# ---------------------------------------------------------------------------
# Modular arithmetic helpers (int64 vectorized)
# ---------------------------------------------------------------------------

def minv(a, p):
    return pow(int(a) % p, p - 2, p)

def minv_vec(a, p):
    """elementwise modular inverse of int64 array a (a != 0 mod p) via Fermat.
    Uses python pow per element but only on small arrays (pivots)."""
    out = np.empty_like(a)
    flat = a.ravel(); o = out.ravel()
    for i in range(flat.size):
        o[i] = pow(int(flat[i]) % p, p - 2, p)
    return out

class FieldE:
    def __init__(self, n, p):
        self.n = n; self.p = p
        validate(n, p)
        pts, omega, g = subgroup(n, p)
        self.pts = pts.astype(np.int64)
        self.omega = omega; self.g = g
        # power table P[i,e] = pts[i]^e mod p, e in 0..n-1
        P = np.ones((n, n), dtype=np.int64)
        for e in range(1, n):
            P[:, e] = (P[:, e-1] * self.pts) % p
        self.P = P

    def word_vals(self, exps, coeffs=None):
        n = self.n; p = self.p
        if coeffs is None:
            coeffs = [1]*len(exps)
        w = np.zeros(n, dtype=np.int64)
        for c, e in zip(coeffs, exps):
            w = (w + (int(c) % p) * self.P[:, e % n]) % p
        return w

    def eval_codewords(self, coeff_mat):
        """coeff_mat: (M, k) int64 of polynomial coeffs (low->high).
        Returns (M, n) int64 of evaluations on mu_n.
        eval = coeff_mat @ V^T  where V[i, j] = pts[i]^j, j<k. Done mod p in int64
        with blocking to avoid overflow in the sum (sum of k terms each < p^2;
        k*p^2 may exceed 2^63 -> reduce per term)."""
        M, k = coeff_mat.shape
        n = self.n; p = self.p
        Vt = self.P[:, :k].T  # (k, n)
        out = np.zeros((M, n), dtype=np.int64)
        for j in range(k):
            out = (out + np.outer(coeff_mat[:, j] % p, Vt[j]) % p) % p
        return out

# ---------------------------------------------------------------------------
# Batched exact interpolation of k-subsets
# ---------------------------------------------------------------------------

def batch_solve(Vbatch, ybatch, p):
    """Solve B independent kxk systems mod p, vectorized.
    Vbatch: (B, k, k) int64 ; ybatch: (B, k) int64. Returns (coeffs (B,k), ok (B,) bool).
    Vectorized Gaussian elimination with partial (any-nonzero) pivot per system."""
    B, k, _ = Vbatch.shape
    A = Vbatch.copy() % p
    b = (ybatch.copy() % p)
    ok = np.ones(B, dtype=bool)
    for col in range(k):
        # find pivot row >= col with nonzero entry, per system
        sub = A[:, col:, col]                  # (B, k-col)
        nz = sub != 0
        has = nz.any(axis=1)
        ok &= has
        # pivot index (first nonzero) relative to col
        piv_rel = np.where(has, nz.argmax(axis=1), 0)
        piv = piv_rel + col
        # swap row col and row piv for each system
        idxB = np.arange(B)
        Arow_col = A[idxB, col, :].copy()
        Arow_piv = A[idxB, piv, :].copy()
        A[idxB, col, :] = Arow_piv
        A[idxB, piv, :] = Arow_col
        bc = b[idxB, col].copy(); bp = b[idxB, piv].copy()
        b[idxB, col] = bp; b[idxB, piv] = bc
        # normalize pivot row
        pivval = A[:, col, col].copy()
        # avoid div by zero where ok is False
        pivval_safe = np.where(pivval % p == 0, 1, pivval)
        inv = np.array([pow(int(v) % p, p-2, p) for v in pivval_safe], dtype=np.int64)
        A[:, col, :] = (A[:, col, :] * inv[:, None]) % p
        b[:, col] = (b[:, col] * inv) % p
        # eliminate this column from all other rows
        for r in range(k):
            if r == col:
                continue
            f = A[:, r, col].copy()
            A[:, r, :] = (A[:, r, :] - f[:, None] * A[:, col, :]) % p
            b[:, r] = (b[:, r] - f * b[:, col]) % p
    return b % p, ok

def count_list_exact(field, wvals, k, tau, batch=20000, return_words=False):
    """EXACT L(w): enumerate all C(n,k) k-subsets in batches, batch-solve, evaluate,
    count agreements, dedup by coeff tuple, keep those with >= tau agreements."""
    n = field.n; p = field.p
    P = field.P
    w = wvals.astype(np.int64)
    seen = set(); good = {}
    subs_iter = combinations(range(n), k)
    buf = []
    def flush(buf):
        if not buf:
            return
        idx = np.array(buf, dtype=np.int64)             # (B, k)
        # Vandermonde of selected points: V[b, r, j] = pts[idx[b,r]]^j
        Vb = P[idx][:, :, :k]                            # (B, k, k)
        yb = w[idx]                                      # (B, k)
        coeffs, ok = batch_solve(Vb, yb, p)             # (B,k),(B,)
        ev = field.eval_codewords(coeffs)               # (B, n)
        agree = (ev == w[None, :]).sum(axis=1)          # (B,)
        for bi in range(idx.shape[0]):
            if not ok[bi]:
                continue
            ct = tuple(int(x) for x in coeffs[bi])
            if ct in seen:
                continue
            seen.add(ct)
            if agree[bi] >= tau:
                good[ct] = int(agree[bi])
    for sub in subs_iter:
        buf.append(sub)
        if len(buf) >= batch:
            flush(buf); buf = []
    flush(buf)
    if return_words:
        return good
    return len(good), good
