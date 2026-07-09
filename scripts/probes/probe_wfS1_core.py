# probe_wfS1_core.py
# Core primitives for CRACK D list-growth experiment (issue #444).
#
# Smooth Reed-Solomon: domain = mu_n = order-n multiplicative subgroup of F_p*,
# n = 2^mu. rate rho = k/n. A codeword = eval on mu_n of a poly g, deg(g) < k.
#
# L(w, delta) = #{ codewords g : agree(g, w) >= (1-delta)*n }.
# Window: delta in (1 - sqrt(rho),  1 - rho - eta_guard).
# We sweep with FIXED gap eta = (1-rho) - delta, so the agreement threshold is
#   tau = (1-delta)*n = (rho + eta)*n   (agreements required).
#
# HONESTY: brute enumeration over codewords is via interpolation on k-subsets of
# agreement points -- but that is C(n,k) which explodes. Instead we use the
# structural fact that worst-case words are lacunary (few terms) and the worst
# codeword list is dominated by low-weight / structured codewords. We provide:
#   (a) exact brute force over ALL codewords for small-k (k<=4) via enumerating
#       all degree-<k polynomials? No -- p is huge. Instead enumerate codewords
#       that agree with w in >= tau points by k-subset interpolation (dedup).
#   (b) lacunary-family lower bound for large (n,k).
#
# All arithmetic mod p with numpy int64 where it fits, else python ints.

import sympy
import numpy as np
from itertools import combinations
from functools import lru_cache

# ----------------------------------------------------------------------------
# Field / subgroup setup
# ----------------------------------------------------------------------------

PRIMES = {16: 65537, 32: 1048609, 64: 16777601, 128: 268437889}

def validate(n, p):
    mu = n.bit_length() - 1
    assert n == 2**mu, f"n={n} not a power of two"
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    assert n < p - 1, f"subgroup not proper: n={n} >= p-1={p-1}"
    assert sympy.isprime(p), f"p={p} not prime"
    return mu

def subgroup(n, p):
    """Return the list of the n-th roots of unity in F_p, as a numpy int64 array,
    ordered by exponent: omega^0, omega^1, ..., omega^{n-1}."""
    g = int(sympy.primitive_root(p))
    omega = pow(g, (p - 1) // n, p)          # primitive n-th root of unity
    pts = np.empty(n, dtype=np.int64)
    cur = 1
    for i in range(n):
        pts[i] = cur
        cur = (cur * omega) % p
    # sanity: distinct, and omega has order exactly n
    assert len(set(pts.tolist())) == n
    assert pow(int(omega), n, p) == 1 and pow(int(omega), n // 2, p) != 1
    return pts, int(omega), g

# ----------------------------------------------------------------------------
# Modular linear algebra (Lagrange / Vandermonde interpolation)
# ----------------------------------------------------------------------------

def interp(xs, ys, p):
    """Interpolate the unique polynomial of degree < len(xs) through (xs,ys) over F_p.
    Returns coefficient list [c0, c1, ...] (low to high). xs distinct mod p."""
    k = len(xs)
    # Build Vandermonde V[i][j] = xs[i]^j, solve V c = ys mod p via Gaussian elim.
    M = [[pow(int(xs[i]), j, p) for j in range(k)] + [int(ys[i]) % p] for i in range(k)]
    # Gaussian elimination mod p
    for col in range(k):
        piv = None
        for r in range(col, k):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return None  # singular (shouldn't happen for distinct xs)
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], p - 2, p)
        M[col] = [(v * inv) % p for v in M[col]]
        for r in range(k):
            if r != col and M[r][col] % p != 0:
                f = M[r][col]
                M[r] = [(M[r][j] - f * M[col][j]) % p for j in range(k + 1)]
    return tuple(M[r][k] % p for r in range(k))

def eval_poly_on_pts(coeffs, pts, p):
    """Evaluate poly (coeff low->high) on array pts (numpy int64) mod p.
    Uses python-int Horner per point to avoid overflow for large p."""
    k = len(coeffs)
    out = np.empty(len(pts), dtype=np.int64)
    cc = [int(c) % p for c in coeffs]
    for idx in range(len(pts)):
        x = int(pts[idx]); acc = 0
        for c in reversed(cc):
            acc = (acc * x + c) % p
        out[idx] = acc
    return out

# ----------------------------------------------------------------------------
# Word representation: a "word" w is an array of n field values on mu_n (by exponent).
# A lacunary word x^a + x^b means w[i] = pts[i]^a + pts[i]^b.
# ----------------------------------------------------------------------------

def word_from_exps(exps, n, pts, p):
    """word = sum_j pts^{exps[j]} (each term coeff 1). exps: list of exponents in [0,n)
    (reduce mod n is NOT done -- caller controls; but on mu_n, pts^a = pts^(a mod n))."""
    w = np.zeros(n, dtype=np.int64)
    for e in exps:
        col = np.empty(n, dtype=np.int64)
        for i in range(n):
            col[i] = pow(int(pts[i]), int(e), p)
        w = (w + col) % p
    return w

# ----------------------------------------------------------------------------
# List counting
# ----------------------------------------------------------------------------

def count_list_exact(w, n, k, pts, p, tau):
    """EXACT L(w): count distinct codewords g (deg<k) agreeing with w in >= tau pts.
    Method: every such codeword is determined by SOME k-subset of its agreement set,
    so it equals interp(k-subset of agreement positions). We enumerate ALL k-subsets
    of {0..n-1}, interpolate, and for each resulting codeword count agreements; keep
    those with >= tau agreements. Dedup by coeff tuple. C(n,k) subsets -- feasible only
    for small C(n,k)."""
    seen = set()
    good = {}
    idx_all = list(range(n))
    w_list = [int(x) % p for x in w]
    for sub in combinations(idx_all, k):
        xs = [int(pts[i]) for i in sub]
        ys = [w_list[i] for i in sub]
        coeffs = interp(xs, ys, p)
        if coeffs is None or coeffs in seen:
            continue
        seen.add(coeffs)
        # count agreements
        ev = eval_poly_on_pts(coeffs, pts, p)
        agree = int(np.sum(ev == w))
        if agree >= tau:
            good[coeffs] = agree
    return good  # dict coeffs -> agreement count

def num_ksubsets(n, k):
    from math import comb
    return comb(n, k)
