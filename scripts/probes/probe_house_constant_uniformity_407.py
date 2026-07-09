#!/usr/bin/env python3
"""probe_house_constant_uniformity_407.py  (#407 — REFUTATION ATTEMPT on a bold conjecture)

BOLD CONJECTURE (to refute): the order-2^a Gauss-period HOUSE constant
    C(p,n) := B(μ_n) / sqrt(n * ln((p-1)/n)),   B = max_{b!=0} |sum_{x in mu_n} e_p(bx)|,
is UNIFORMLY BOUNDED by an absolute constant (empirically ~1.33, i.e. C^2 <~ 1.75) for ALL primes
p == 1 mod n in the sparse regime p >> n^2.5 — with NO bad-prime spikes.

If true (uniform, no spikes): the closed-form delta* is q-INDEPENDENT and a clean constant-form
conjecture is at least STATEABLE with a definite constant.  If FALSE (spikes at bad primes): every
constant-form closed conjecture for delta* is REFUTED — delta* genuinely depends on the arithmetic of
p (bad-prime coincidences), exactly as the additive ENERGY does (E=3n(n-1) generically, but spikes at
bad primes).  Either outcome is a real finding.

METHOD: for each n=2^a, scan MANY primes p==1 mod n across the sparse band; compute B exactly (FFT);
track the WORST-CASE C and the prime achieving it; flag any C > sqrt(2) (~1.414) and any C > 1.33.
Contrast the WORST C against the MEDIAN C (a spike shows as worst >> median).
"""
import numpy as np, math
from statistics import median

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(w, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True

def subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s, x = set(), 1
        for _ in range(n):
            s.add(x); x = x*h % p
        if len(s) == n: return sorted(s)
    return None

def house(p, n, H):
    f = np.zeros(p)
    for x in H: f[x] = 1.0
    S = np.fft.fft(f)
    a = np.abs(S); a[0] = 0.0
    return float(np.max(a))

print("Worst-case Gauss-period house constant C = B / sqrt(n*ln((p-1)/n)) over a prime scan.")
print("(sparse band p in [n^2.6, n^3.4]; flag C>1.33 and C>sqrt(2)=1.414)")
print(f"{'n':>4} | {'#primes':>7} {'medianC':>8} {'WORST C':>8} {'@p':>10} {'maxC>sqrt2?':>11}")
sqrt2 = math.sqrt(2)
for a in range(3, 8):
    n = 2**a
    lo = int(n**2.6); hi = min(int(n**3.4), 2_500_000)
    Cs = []
    worst = (0.0, None)
    p = lo - (lo % n) + 1
    cnt = 0
    while p <= hi:
        if (p-1) % n == 0 and is_prime(p):
            H = subgroup(p, n)
            if H:
                m = (p-1)//n
                B = house(p, n, H)
                C = B / math.sqrt(n * math.log(m))
                Cs.append(C); cnt += 1
                if C > worst[0]: worst = (C, p)
        p += n
        if cnt >= 120: break
    if Cs:
        flag = "YES(REFUTED)" if worst[0] > sqrt2 else "no"
        print(f"{n:>4} | {cnt:>7} {median(Cs):>8.3f} {worst[0]:>8.3f} {worst[1]:>10} {flag:>11}")

print("\nNOW THE BAD-PRIME HUNT: scan SMALL sparse primes densely (where coincidences concentrate),")
print("looking for any C spike (analogous to the additive-energy bad primes).")
for a in (3, 4, 5):
    n = 2**a
    worst = (0.0, None); allC = []
    p = n + 1
    while p < max(60000, n**3):
        if (p-1) % n == 0 and is_prime(p) and p > int(n**2.5):  # sparse only
            H = subgroup(p, n)
            if H:
                m = (p-1)//n
                C = house(p, n, H) / math.sqrt(n*math.log(m))
                allC.append(C)
                if C > worst[0]: worst = (C, p)
        p += 1
    if allC:
        print(f"  n={n}: sparse primes={len(allC)}, median C={median(allC):.3f}, "
              f"WORST C={worst[0]:.3f} @ p={worst[1]}, "
              f"{'SPIKE>sqrt2' if worst[0]>sqrt2 else 'bounded<=sqrt2'}")
print("\nVERDICT: worst C bounded (<sqrt2) and ~ median  => no spikes => constant-form conjecture")
print("         survives (stateable, still unprovable). worst C >> median or > sqrt2 => REFUTED.")
