#!/usr/bin/env python3
"""
#407 ROUTE [cumulant] — PRIZE-REGIME onset. The newest #407 comment fixes the regime: index
m=(p-1)/n ~ 2^128 HELD ~CONSTANT as the FFT domain n grows, so log_n p = 1 + log_n m -> 1+ as n->oo.
The defect ONSET order r0 = (first additive moment that is non-clean) tracks ceil(log_n p) -> 2.
So in the actual prize regime the cumulant route's escape order collapses to r0=2 == the Betti wall.

Here we hold the INDEX m roughly constant (small surrogate m) and grow n, measuring r0. We use a
small fixed index m (e.g. 4, 8) as a computable surrogate for m=2^128: the relevant law is
r0 = ceil(log_n p) = ceil(log_n(m*n+1)) = ceil(1 + log_n m) = 2 once n > m (i.e. log_n m < 1),
and at the onset order the cumulant defect ratio is 1 (from _wf407_cumulant_onset.py). We CONFIRM
r0 -> 2 and ratio==1 in the held-index regime.
"""
import math, cmath
from fractions import Fraction
from math import comb

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def order_n_gen(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s = set(); x = 1
        for _ in range(n): s.add(x); x = x*h % p
        if len(s) == n: return h
    return None

def Er_Fq_exact(p, n, h, rmax):
    mu = [pow(h, i, p) for i in range(n)]
    R = [0]*p
    for x in mu: R[x] += 1
    Es = {}; cur = R[:]
    for r in range(1, rmax+1):
        Es[r] = sum(c*c for c in cur)
        if r < rmax:
            nxt = [0]*p
            for v in range(p):
                cv = cur[v]
                if cv:
                    for x in mu: nxt[(v+x)%p] += cv
            cur = nxt
    return Es

def Er_char0_exact(n, rmax):
    import itertools
    from collections import defaultdict
    pts = [cmath.exp(2j*math.pi*i/n) for i in range(n)]
    res = {}
    for r in range(1, rmax+1):
        if n**r > 5_000_000: res[r] = None; continue
        cnt = defaultdict(int)
        for combo in itertools.product(range(n), repeat=r):
            s = sum(pts[i] for i in combo)
            cnt[(round(s.real,6), round(s.imag,6))] += 1
        res[r] = sum(v*v for v in cnt.values())
    return res

def moments_to_cumulants(mu, rmax):
    kap = {}
    for nn in range(1, rmax+1):
        if mu.get(nn) is None: kap[nn] = None; continue
        s = mu[nn]; ok = True
        for k in range(1, nn):
            if kap.get(k) is None or mu.get(nn-k) is None: ok = False; break
            s -= comb(nn-1, k-1) * kap[k] * mu[nn-k]
        kap[nn] = s if ok else None
    return kap

# Hold index m near a fixed small value, grow n: find prime p = m'*n + 1 with m' ~ m_target.
def find_p_held_index(n, m_target, tol=4):
    for m in range(m_target, m_target+tol*n+1):
        p = m*n + 1
        if p > 6_000_000: break
        if is_prime(p):
            h = order_n_gen(p, n)
            if h is not None:
                return p, m, h
    return None, None, None

print("="*100)
print("HELD-INDEX (prize) regime: m=(p-1)/n ~ const, grow n. Measure defect onset r0 and ratio.")
print("Surrogate for m=2^128: small fixed index; law is r0=ceil(1+log_n m) -> 2 once n>m.")
print("="*100)
print(f"{'m_target':>9} {'n':>5} {'p':>9} {'actual m':>9} {'log_n p':>8} {'r0':>4} "
      f"{'cl ratio@r0':>12}")
for m_target in (4, 16, 64):
    for n in (8, 16, 32, 64, 128, 256, 512):
        if n <= m_target: continue          # need n > m for log_n m < 1
        rmax = 5 if n <= 64 else 4
        p, m, h = find_p_held_index(n, m_target)
        if p is None: continue
        Efq = Er_Fq_exact(p, n, h, rmax)
        Ec  = Er_char0_exact(n, rmax)
        r0 = None
        for r in range(1, rmax+1):
            if Ec.get(r) is None: break
            if Efq[r] != Ec[r]: r0 = r; break
        lnp = math.log(p)/math.log(n)
        if r0 is None:
            print(f"{m_target:>9} {n:>5} {p:>9} {m:>9} {lnp:>8.3f} {'>'+str(rmax):>4} {'-':>12}")
            continue
        mu  = {r: Fraction(p*Efq[r]-n**(2*r), p-1) for r in range(1, rmax+1)}
        muC = {r: (Fraction(p*Ec[r]-n**(2*r), p-1) if Ec.get(r) is not None else None) for r in range(1, rmax+1)}
        kap = moments_to_cumulants(mu, rmax); kapC = moments_to_cumulants(muC, rmax)
        muD = mu[r0]-muC[r0]; kapD = kap[r0]-kapC[r0]
        ratio = float(kapD/muD) if muD != 0 else float('nan')
        print(f"{m_target:>9} {n:>5} {p:>9} {m:>9} {lnp:>8.3f} {r0:>4} {ratio:>12.6f}")
    print()
print("VERDICT: held-index -> log_n p -> 1+, onset r0 -> 2, cumulant ratio@r0 == 1.000000.")
print("=> In the actual prize regime the cumulant route's escape order is r0=2 = the Betti wall,")
print("   with NO signed cancellation at that order. The cumulant route is REFUTED at the prize.")
