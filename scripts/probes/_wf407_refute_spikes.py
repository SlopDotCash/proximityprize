#!/usr/bin/env python3
"""
#407 ADVERSARIAL REFUTATION, part 2 — can the KNOWN spike GROW with n?

The campaign found p=65537 (Fermat prime, m = 2^16/n a pure power of 2) gives
C=R=2.07 at n=64 -- a near-threshold spike (p/n^2.5 ~ 2). The refutation
question that matters for the prize:  is the spike a FIXED near-threshold
artifact (C bounded), or does the worst-case C GROW with n along a family?

We test families designed to MAXIMIZE R:
  (A) FERMAT primes / Proth primes p = c*2^a+1 with SMALL odd part of m
      (m = (p-1)/n; if m | 2^k then ALL m periods are 'aligned' -> big B).
  (B) p where 2 has SMALL multiplicative order (sparse 2-power structure).
  (C) the 'pure 2-power m' diagonal: choose n=2^mu, p with v2(p-1) just above mu
      so m = (p-1)/n has m = 2^(v2(p-1)-mu) * odd, odd part minimal.

For each, we sweep n upward as far as exact compute allows and record R(n).
If R(n) trends UP -> conjecture B<=C sqrt(n ln m) is REFUTED (C unbounded).
If R(n) saturates/declines -> spike is a bounded near-threshold artifact.
"""
import math
import numpy as np
from sympy import isprime, primitive_root, factorint

P = lambda *a, **k: print(*a, flush=True, **k)

def floor_B(p, n, g=None):
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64); cur = 1
    for k in range(n): mu[k] = cur; cur = cur*gm % p
    tp = 2.0*math.pi/p
    best = 0.0; r = 1
    for _ in range(m):
        pr = (r*mu) % p
        s = np.cos(tp*pr).sum() + 1j*np.sin(tp*pr).sum()
        a = abs(s)
        if a > best: best = a
        r = r*g % p
    return best, m

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x

# ---------------------------------------------------------------
P("="*78)
P("REFUTATION pt2 — does the worst-case spike GROW with n?")
P("="*78)

# (A) Fermat prime p=65537: m=(p-1)/n is a pure power of 2 for n | 2^16.
P("\n--- (A) Fermat prime p=65537=2^16+1: m pure power of 2, n=2^mu ---")
P(f"  {'n':>5} {'m':>7} {'B':>10} {'sqrt(n ln m)':>13} {'R':>8} {'B/sqrt(n)':>10}")
p = 65537
for mu in range(1, 16):
    n = 1 << mu
    m = (p-1)//n
    if m < 2: continue
    B, _ = floor_B(p, n)
    den = math.sqrt(n*math.log(m))
    P(f"  {n:>5} {m:>7} {B:>10.4f} {den:>13.4f} {B/den:>8.4f} {B/math.sqrt(n):>10.4f}")

# Fermat prime p=4294967297? not prime (641*...). The next true Fermat is only F0..F4.
# F4 = 65537 is the largest Fermat prime. So the 'pure 2^a+1 prime' family is FINITE.
P("\n  NOTE: F4=65537 is the LARGEST Fermat prime (F5..unknown all composite).")
P("        So 'p = 2^a+1 prime' gives NO larger n. The pure-power-of-2 m diagonal")
P("        must instead use Proth primes p=c*2^a+1, c>1 odd (m has odd part = c).")

# (C) Proth-diagonal: for each n=2^mu, find primes p=c*2^a+1 with a>mu and
#     odd part of m = (p-1)/n = c minimized (c=1 impossible beyond Fermat, so c=3,5,..).
#     This maximizes the 2-power alignment of the m periods. Sweep n up.
P("\n--- (C) Proth diagonal: n=2^mu, minimal-odd-part m, p=c*2^a+1 ---")
P("  for each n, search c in {1,3,5,..} and a>mu for smallest prime keeping p small;")
P("  record R and whether it spikes. (worst over a small (c,a) window)")
P(f"  {'n':>5} {'best_p':>10} {'m':>9} {'oddpart(m)':>10} {'v2(m)':>6} {'B':>10} {'R':>8} {'shallow':>8}")
for mu in range(3, 11):   # n = 8..1024
    n = 1 << mu
    bestR = -1; best = None
    # search small Proth primes p = c*2^a + 1, a from mu+1.. with p not too large
    for a in range(mu+1, mu+15):
        for c in range(1, 200, 2):
            p = c*(1<<a) + 1
            if p > 6_000_000: break
            if not isprime(p): continue
            if (p-1) % n != 0: continue
            m = (p-1)//n
            if m < 2: continue
            if m*n > 6_000_000: continue
            B, _ = floor_B(p, n)
            R = B/math.sqrt(n*math.log(m))
            op = odd_part(m); v = (m & -m).bit_length()-1
            if R > bestR:
                bestR = R; best = (p,m,op,v,B,R,p/n**2.5)
    if best:
        pp,m,op,v,B,R,sh = best
        P(f"  {n:>5} {pp:>10} {m:>9} {op:>10} {v:>6} {B:>10.4f} {R:>8.4f} {sh:>8.2f}")
    else:
        P(f"  {n:>5}  (no prime found in window)")

# (B) primes where 2 has small order: p | 2^k - 1 (so ord_p(2)=k small relative to p).
#     These are the 'repunit-in-base-2' primes; their multiplicative structure is
#     special. Test a handful with subgroups of various n.
P("\n--- (B) primes p | (2^k - 1) [small ord_2]: worst R over n | (p-1) ---")
P(f"  {'p':>10} {'ord2':>6} {'n':>6} {'m':>9} {'B':>10} {'R':>8} {'shallow':>8}")
import sympy
seen=set()
for k in range(8, 60):
    M = (1<<k) - 1
    for q in factorint(M):
        if q in seen or q < 100: continue
        seen.add(q)
        p = q
        if p > 3_000_000: continue
        # ord_2(p) divides k
        o2 = k
        # sweep n = powers of 2 dividing p-1
        v2p = (p-1 & -(p-1)).bit_length()-1
        for mu in range(3, v2p+1):
            n = 1<<mu
            if (p-1)%n!=0: continue
            m=(p-1)//n
            if m<2 or m*n>5_000_000: continue
            B,_=floor_B(p,n)
            R=B/math.sqrt(n*math.log(m))
            if R>1.5:
                P(f"  {p:>10} {o2:>6} {n:>6} {m:>9} {B:>10.4f} {R:>8.4f} {p/n**2.5:>8.2f}  <- R>1.5")

P("\nDONE pt2.")
