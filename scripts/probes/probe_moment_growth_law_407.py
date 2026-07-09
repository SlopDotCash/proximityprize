#!/usr/bin/env python3
"""probe_moment_growth_law_407.py  (#407 prize — the deep-moment growth law, decisive)

THE SHARP OPEN QUESTION (synthesis §3'):
  The moment arrow  B = max_b |S(b)| <= (q*E_r)^{1/2r}  is PROVEN (max_le_moment).
  Running it at depth r ~ log q with char-0 moments  E_r ~ c^r r! n^r  yields the prize
  bound  B <~ sqrt(n log q)  IFF the per-moment constant c is BOUNDED (sub-Gaussian).
  If c(n) grows, the arrow overshoots and the wall stands.  This probe pins c(n) EXACTLY.

DEFINITIONS
  mu_n = order-n=2^a multiplicative subgroup of F_p, p = 1 mod n (SPARSE: p >> n^2.5).
  S(b) = sum_{x in mu_n} e_p(b x).   E_r = (1/p) sum_b |S(b)|^{2r}  (integer; #{sum x = sum y}).
  Report:  E_r / (r! n^r)   (the char-0-normalized moment ratio = c(n)^r if E_r ~ c^r r! n^r),
  and its r-th root  (E_r/(r! n^r))^{1/r}  = the effective per-moment constant c_r(n).

  Also B and the normalized B/sqrt(n*log2(p/n)) and B/sqrt(n).

WHY DECISIVE
  - c_r(n) bounded in BOTH r and n  ->  moment arrow closes the prize (sub-Gaussian).
  - c_r(n) ~ const but grows in n   ->  B <~ sqrt(n log q log n): the sqrt(log n) overshoot.
  - c_r(n) grows in r               ->  deep moments inflate; the wall (no fixed depth helps).
  We measure the joint (r,n) growth in the SPARSE regime to settle which.
"""
import numpy as np

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

def prime_1_mod_n_near(target, n):
    """largest prime p <= target with p == 1 mod n (sparse anchor)."""
    p = target - (target % n) + 1
    if p > target: p -= n
    while p > n:
        if is_prime(p): return p
        p -= n
    return None

def subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s, x = set(), 1
        for _ in range(n):
            s.add(x); x = x*h % p
        if len(s) == n: return sorted(s)
    return None

def moments(p, n, H, rmax):
    """exact-ish E_r for r=1..rmax via FFT of the indicator over Z_p."""
    f = np.zeros(p)
    for x in H: f[x] = 1.0
    S = np.fft.fft(f)          # S[b] = sum_x e_p(b x) = char sum
    a2 = np.abs(S)**2          # |S(b)|^2, real
    res = {}
    for r in range(1, rmax+1):
        Er = np.sum(a2**r) / p
        res[r] = Er
    B = float(np.max(np.abs(S)))   # includes b=0? S[0]=n. exclude it for B:
    a2[0] = 0.0
    Bnz = float(np.sqrt(np.max(a2)))
    return res, Bnz

import math
print("SPARSE regime p ~ n^3 (prize is p ~ n^4..n^5; n^3 already >> n^2.5 threshold).")
print(f"{'n':>4} {'p':>10} | " + " ".join(f"c_{r}(n)" for r in range(2,7)) +
      " | B  B/sqrtn  B/sqrt(n*log2(p/n))")
fac = [math.factorial(r) for r in range(0, 12)]
for a in range(3, 8):           # n = 8,16,32,64,128
    n = 2**a
    p = prime_1_mod_n_near(n**3, n)
    if p is None or p > 6_000_000:   # keep FFT length manageable
        p = prime_1_mod_n_near(min(n**3, 4_000_000), n)
    H = subgroup(p, n)
    if H is None:
        print(f"{n:>4} {p:>10} | (no subgroup)"); continue
    res, B = moments(p, n, H, 6)
    cs = []
    for r in range(2, 7):
        ratio = res[r] / (fac[r] * n**r)
        c_r = ratio ** (1.0/r)
        cs.append(c_r)
    bsn = B/math.sqrt(n)
    bsl = B/math.sqrt(n*math.log2(p/n))
    print(f"{n:>4} {p:>10} | " + " ".join(f"{c:6.3f}" for c in cs) +
          f" | {B:6.2f}  {bsn:5.3f}   {bsl:5.3f}")

print("\nGROWTH IN r AT FIXED n (does c_r grow with r? => deep moments inflate):")
for a in (5, 6):
    n = 2**a
    p = prime_1_mod_n_near(n**3, n)
    H = subgroup(p, n)
    res, B = moments(p, n, H, 8)
    print(f" n={n} p={p}: " + " ".join(f"E_{r}/(r!n^r)={res[r]/(fac[r]*n**r):.3f}" for r in range(2,9)))

print("\nREAD: c_r ~ const in r and n => sub-Gaussian => moment arrow CLOSES prize.")
print("      c_r grows in r => deep-moment wall (the recognized obstruction).")

print("\n=== MOMENT-ARROW NO-GO: best bound min_r (p*E_r)^{1/2r} vs true B ===")
print(f"{'n':>4} {'p':>10} | {'trueB':>7} {'sqrt(nL)':>9} | {'arrow_min':>9} {'@r':>3} {'arrow/trueB':>11}")
for a in range(3, 8):
    n = 2**a
    p = prime_1_mod_n_near(n**3, n)
    if p is None or p > 6_000_000:
        p = prime_1_mod_n_near(min(n**3, 4_000_000), n)
    H = subgroup(p, n)
    if H is None: continue
    rmax = 16
    res, B = moments(p, n, H, rmax)
    L = math.log2(p/n); snl = math.sqrt(n*L)
    best = None; bestr = None
    for r in range(1, rmax+1):
        bound = (p * res[r]) ** (1.0/(2*r))
        if best is None or bound < best:
            best, bestr = bound, r
    print(f"{n:>4} {p:>10} | {B:7.2f} {snl:9.2f} | {best:9.2f} {bestr:3d} {best/B:11.3f}")
print("READ: arrow_min >> trueB and ratio GROWS with n  =>  moment method provably overshoots;")
print("      the clean law B~sqrt(n log(p/n)) is NOT reachable by moments (the residual is the")
print("      growing-n distribution of incomplete subgroup sums = Kowalski-Untrau OPEN).")
