#!/usr/bin/env python3
"""ANGLE B: injection {distinct nonzero bad gamma} -> {signed r-subsets of mu_{n/2}}.

K = 2^r * C(n/2, r) = #{signed r-subsets of mu_{n/2}}.

Setup (calibrated against in-tree DeepBandR3Bound + r4/r5 maximizer O_P):
  - mu_n = order-n subgroup of F_p*, w = generator of order n, dom[i]=w^i.
  - bad S (size r+1) for line (x^e,x^f) <=> h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S) (V)
    AND h_{f-r}(S) != 0; pinned gamma = -h_{e-r}(S)/h_{f-r}(S).
  - gamma(gS) = g^{e-f} gamma(S), so distinct gammas come in dilation orbits of size n/d, d=gcd(e-f,n).

DESCENT CONVOLUTION: w of order n; w^{n/2} = -1 (since w^{n/2} has order 2). Pair each element
z=w^i with its antipode -z = w^{i+n/2}. An (r+1)-subset S of mu_n splits into:
  - PAIRS P: antipodal pairs {z,-z} fully inside S
  - SINGLETONS T: elements of S whose antipode is NOT in S
If S has 'a' pairs and 'b' singletons, then |S| = 2a+b = r+1.
For pairs, z*(-z) = -z^2; the pair-square set SQ = {z^2 : {z,-z} subset S}, |SQ| = a, SQ subset mu_{n/2}.
Convolution identity (since prod_{z in pair}(1-zt)(1+zt) = prod (1 - z^2 t^2)):
  h_m(S) = sum_{s>=0} h_s(SQ over t^2) * h_{m-2s}(T)
where h_s(SQ) is complete-homog of the SQUARES (in mu_{n/2}), evaluated in variable t^2.
Concretely: H_S(t) = 1/prod_{z in S}(1-zt) = [1/prod_{q in SQ}(1-q t^2)] * [1/prod_{u in T}(1-u t)].
So h_m(S) = sum_s hSQ_s * hT_{m-2s}, hSQ_s = h_s of the squares, hT_j = h_j of singletons.

This probe:
 (1) calibrates r=3 maximizer -> reproduce #bad and the C(n/4,2) structure
 (2) verifies the convolution identity numerically
 (3) tests Angle B injection: does gamma determine a UNIQUE signed r-subset of mu_{n/2}?
"""
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict
p = 2013265921
P2 = 3221225473  # cross-check prime

def setup(n, prime=p):
    e = (prime - 1) // n
    for c in range(2, 400):
        h = pow(c, e, prime)
        if pow(h, n, prime) == 1 and pow(h, n // 2, prime) != 1:
            dom = [pow(h, i, prime) for i in range(n)]
            return dom, h
    raise RuntimeError("no generator")

def h_upto(Sv, M, prime=p):
    """complete homogeneous h_0..h_M of multiset Sv via forward recurrence H[m]+=z*H[m-1]."""
    h = [0] * (M + 1); h[0] = 1
    for z in Sv:
        prev = 0
        for m in range(M + 1):
            cur = (h[m] + z * prev) % prime
            prev = h[m]
            h[m] = cur
    return h

def bad_gamma(Sv, e, f, r, prime=p):
    """Return pinned gamma if S is bad (on V, h_{f-r}!=0), else None. None also if degenerate."""
    M = max(e - r, e - r + 1, f - r, f - r + 1, 0)
    hv = h_upto(Sv, M, prime)
    H = lambda m: hv[m] if 0 <= m <= M else 0
    her, her1, hfr, hfr1 = H(e - r), H(e - r + 1), H(f - r), H(f - r + 1)
    if (her * hfr1 - hfr * her1) % prime != 0:
        return None
    if hfr % prime == 0:
        return None  # gamma undefined (inf) — excluded
    g = (-her * pow(hfr, prime - 2, prime)) % prime
    return g

# ---------- calibration r=3 ----------
def calibrate_r3():
    print("=== CALIBRATION r=3 (bilinear-line model) ===")
    r = 3
    for n in (16, 32):
        dom, w = setup(n)
        # r=3 maximizer line for the *bilinear* model. CONTEXT: r4 line (x^{n/2+2},x^{n/4+1}).
        # For r=3, scan |e-f| small lines to find the bad-max; report O_P structure.
        best = None
        for e in range(r, n):
            for f in range(r - 1, n):
                if e == f: continue
                u_e = e; u_f = f
                gammas = set()
                for S in combinations(range(n), r + 1):
                    Sv = [dom[i] for i in S]
                    g = bad_gamma(Sv, u_e, u_f, r)
                    if g is not None and g != 0:
                        gammas.add(g)
                cnt = len(gammas)
                if best is None or cnt > best[0]:
                    best = (cnt, e, f, set(gammas))
        cnt, e, f, gammas = best
        d = gcd(e - f, n)
        OP = cnt // (n // d)
        print(f"  n={n}: bilinear r=3 max line (x^{e},x^{f}) d={d}: #bad(nz)={cnt}  n/d={n//d}  O_P={OP}  "
              f"C(n/4,2)={comb(n//4,2)}")
    print()

if __name__ == "__main__":
    calibrate_r3()
