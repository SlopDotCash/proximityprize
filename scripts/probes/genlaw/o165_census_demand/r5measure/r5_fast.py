#!/usr/bin/env python3
"""
r5_fast.py — faster variety-only measurement for larger n (32, 64), with r=3 self-check.
Uses the h_m Schur-ratio variety V exclusively (cross-checked against interp at n=16 already).
Optimizations:
  - precompute dom powers; h_vec computed incrementally needs only h up to M = max(e-r+1, f-r+1).
  - for the maximizer line (e,f)=(n/2+1, n-1), r=5: indices e-r=n/2-4, f-r=n-6, etc. -> M ~ n-5.
    That's expensive. Instead compute the FULL h vector once per S via the elementary-symmetric route?
    Simpler: h_m only needs m up to max index. We compute h via the recurrence but vectorized in C-ints.
"""
from math import comb, gcd
from itertools import combinations
from collections import Counter
import sys

p = 2013265921

def mu_n(n, prime):
    e = (prime - 1) // n
    for c in range(2, 400):
        h = pow(c, e, prime)
        if pow(h, n, prime) == 1 and pow(h, n // 2, prime) != 1:
            return [pow(h, i, prime) for i in range(n)]
    raise RuntimeError("no generator")

def h_upto(Sv, M, prime):
    """h_0..h_M, h_m=[t^m] prod 1/(1-z t).  Incremental: for each z multiply by 1/(1-z t)."""
    h = [0]*(M+1); h[0] = 1
    for z in Sv:
        # multiply by sum_k z^k t^k : new_m = sum_{j<=m} h_j z^{m-j}
        # do it via: new = h convolved with geometric; recurrence new_m = h_m + z*new_{m-1}
        new = [0]*(M+1)
        prev = 0
        for m in range(M+1):
            prev = (h[m] + z*prev) % prime
            new[m] = prev
        h = new
    return h

def measure_variety(n, e, f, r, prime):
    a0 = r+1; k = r-1
    dom = mu_n(n, prime)
    idxs = [e-r, e-r+1, f-r, f-r+1]
    M = max([i for i in idxs] + [0])
    K = (1 << r)*comb(n//2, r)
    gammas = Counter(); S_on_V = 0; gamma0 = 0
    for S in combinations(range(n), a0):
        Sv = [dom[i] for i in S]
        hv = h_upto(Sv, M, prime)
        def H(m): return hv[m] if 0 <= m <= M else 0
        her, her1 = H(e-r), H(e-r+1)
        hfr, hfr1 = H(f-r), H(f-r+1)
        if (her*hfr1 - hfr*her1) % prime != 0: continue
        if hfr == 0: continue
        S_on_V += 1
        gam = (-her*pow(hfr, prime-2, prime)) % prime
        gammas[gam] += 1
        if gam == 0: gamma0 += 1
    d = gcd(e-f, n); orbit = n//d
    distinct_nonzero = len([g for g in gammas if g != 0])
    nbad = distinct_nonzero + (1 if 0 in gammas else 0)
    fib = sorted(gammas.values())
    fibdist = dict(sorted(Counter(fib).items()))
    OP = distinct_nonzero // orbit if distinct_nonzero % orbit == 0 else None
    return dict(n=n, e=e, f=f, K=K, S_on_V=S_on_V, nbad=nbad,
                distinct_nonzero=distinct_nonzero, gamma0=(0 in gammas),
                d=d, orbit=orbit, OP=OP, fibmin=min(fib), fibmax=max(fib),
                fibdist=fibdist, total_S=sum(fib))

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [32]
    # r=3 self-check (variety path) at n=16
    chk = measure_variety(16, 8, 7, 3, p)
    assert chk['nbad'] == 97, f"r3 selfcheck FAIL {chk['nbad']}"
    print(f"[selfcheck r=3 n=16] #bad={chk['nbad']} (==97 OK)  #S_on_V={chk['S_on_V']}")
    r = 5
    for n in ns:
        e, f = n//2 + 1, n - 1
        res = measure_variety(n, e, f, r, p)
        print(f"\n=== r=5 n={n} line(x^{e},x^{f}) ===")
        print(f"  K=2^r C(n/2,r) = {res['K']}")
        print(f"  #S_on_V          = {res['S_on_V']}")
        print(f"  #bad (distinct gamma, incl 0?) = {res['nbad']}  (nonzero={res['distinct_nonzero']}, gamma0={res['gamma0']})")
        print(f"  d=gcd(e-f,n)={res['d']} orbit=n/d={res['orbit']}  O_P={res['OP']}")
        print(f"  #S_on_V<=K ? {res['S_on_V']<=res['K']}   K/#S_on_V={res['K']/max(res['S_on_V'],1):.3f}")
        print(f"  #S_on_V/#bad = {res['S_on_V']/max(res['nbad'],1):.3f}   #bad<=#S_on_V ? {res['nbad']<=res['S_on_V']}")
        print(f"  fiber dist {{size:count}} = {res['fibdist']}  (min={res['fibmin']} max={res['fibmax']}) total_S={res['total_S']}")
        print(f"  fiber constant == orbit({res['orbit']})? {set(res['fibdist'].keys())=={res['orbit']}}")
