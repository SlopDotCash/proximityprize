#!/usr/bin/env python3
"""probe_house_2adic_dependence_407.py  (#407 — does the house constant depend on v2(m)?)

The uniform-constant conjecture was REFUTED (spike C=2.07 at the Fermat prime p=65537, n=64,
m=2^10 a pure power of 2 -- but only ~2x the n^2.5 threshold).  Here: within a DEEP-sparse band at
fixed n (p >> n^2.5), bin the house constant C=B/sqrt(n*ln m) by the excess 2-adic smoothness
v2(m)=v2(p-1)-a (m=(p-1)/n).  If max C rises with v2(m) deep-sparse, delta*'s constant is governed by
the 2-adic structure of (p-1)/n; if flat, the 65537 spike was a near-threshold artifact.
"""
import sys, numpy as np, math
from statistics import median

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        if x % w == 0: return x == w
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37,41,43):
        v = pow(w, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True

def v2(x):
    k = 0
    while x % 2 == 0: x //= 2; k += 1
    return k

def subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s, x = set(), 1
        for _ in range(n):
            s.add(x); x = x*h % p
        if len(s) == n: return sorted(s)
    return None

def house_C(p, n):
    H = subgroup(p, n)
    if H is None: return None
    f = np.zeros(p)
    for x in H: f[x] = 1.0
    a = np.abs(np.fft.fft(f)); a[0] = 0.0
    return float(np.max(a)) / math.sqrt(n * math.log((p-1)//n))

PMAX = 3_000_000   # FFT length cap
# (n, lo, hi) deep-sparse bands with p >> n^2.5
bands = [(16, 60_000, 1_500_000), (32, 120_000, 3_000_000), (64, 300_000, 3_000_000)]
for n, lo, hi in bands:
    a = int(round(math.log2(n)))
    thr = n**2.5
    bins = {}
    p = lo - (lo % n) + 1
    seen = 0
    while p <= min(hi, PMAX) and seen < 500:
        if (p-1) % n == 0 and is_prime(p):
            C = house_C(p, n)
            if C is not None:
                bins.setdefault(v2((p-1)//n), []).append((C, p))
                seen += 1
        p += n
    print(f"n={n}  band[{lo},{min(hi,PMAX)}]  p/n^2.5 in [{lo/thr:.0f},{min(hi,PMAX)/thr:.0f}]  ({seen} primes):", flush=True)
    for vm in sorted(bins):
        cs = [c for c, _ in bins[vm]]
        wC, wp = max(bins[vm])
        print(f"   v2(m)={vm:2d}: #={len(cs):3d}  medianC={median(cs):.3f}  maxC={wC:.3f} @p={wp}", flush=True)
    # the single worst prime in the whole band and its v2
    allp = [(c, p_, vm) for vm, lst in bins.items() for c, p_ in lst]
    if allp:
        wc, wp, wv = max((c, p_, vm) for vm, lst in bins.items() for c, p_ in lst)
        print(f"   >>> WORST in band: C={wc:.3f} @p={wp}, v2(m)={wv}  (median over band={median([c for c,_,_ in allp]):.3f})", flush=True)
print("\nReference Fermat primes (shallow, p-1 a pure 2-power -> m pure 2-power):", flush=True)
for p in (257, 65537):
    for a in range(3, 8):
        n = 2**a
        if (p-1) % n == 0 and p > n:
            C = house_C(p, n)
            print(f"   p={p} (=2^{int(math.log2(p-1))}+1) n={n} m={(p-1)//n}=2^{v2((p-1)//n)} : C={C:.3f}  p/n^2.5={p/n**2.5:.1f}", flush=True)
