#!/usr/bin/env python3
"""
#407 ADVERSARIAL REFUTATION of the prize floor  B <= C * sqrt(n * ln m).

p prime, p-1 = m*n, mu_n = order-n subgroup of F_p^*.
B = max_{b!=0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b*x).
R = B / sqrt(n * ln m). Conjecture: R bounded. We HUNT for spikes/growth.

Coset reduction: eta constant on cosets b*mu_n -> exact B = max over m coset reps.
"""
import math, sys
import numpy as np
from sympy import isprime, primitive_root, factorint

P = lambda *a, **k: print(*a, flush=True, **k)

def floor_B(p, n, g=None):
    """Exact B = max_{b!=0}|eta_b| via scan over m coset reps (float64 mag)."""
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64); cur = 1
    for k in range(n): mu[k] = cur; cur = cur*gm % p
    tp = 2.0*math.pi/p
    best = 0.0; bestb = 1; r = 1
    for _ in range(m):
        pr = (r*mu) % p
        s = np.cos(tp*pr).sum() + 1j*np.sin(tp*pr).sum()
        a = abs(s)
        if a > best: best = a; bestb = r
        r = r*g % p
    return best, m, bestb

def R_of(p, n, g=None):
    B, m, b = floor_B(p, n, g)
    if m < 2: return None
    return B/math.sqrt(n*math.log(m)), B, m, b

def v2(x):
    return (x & -x).bit_length()-1

# ----------------------------------------------------------------------
P("="*78)
P("ADVERSARIAL REFUTATION SWEEP  R = B / sqrt(n ln m)   (hunting for spikes)")
P("="*78)

ns = [8,16,32,64,128,256]
# work budget: scan over m for each n, p = n*m+1 prime, p <= PCAP.
# This enumerates ALL primes p with p-1 divisible by n, exactly.
PCAP = 5_000_000
WORK_CAP = 7_000_000   # cap m*n = p for the dense scan per instance

records = []
total = 0
for n in ns:
    mmax = min((PCAP-1)//n, WORK_CAP//n)
    for m in range(2, mmax+1):
        p = n*m + 1
        if not isprime(p): continue
        g = primitive_root(p)
        r = R_of(p, n, g)
        if r is None: continue
        R, B, mm, b = r
        records.append(dict(R=R,B=B,p=p,n=n,m=m,b=b,v2m=v2(m),
                            shallow=p/(n**2.5)))
        total += 1

P(f"\n# total (p,n) instances scanned exactly: {total}")

# ---- WORST per n ----
P("\n--- WORST R per n (adversarial max over ALL valid primes p<5e6) ---")
P(f"{'n':>5} {'R':>8} {'B':>9} {'p':>9} {'m':>8} {'v2(m)':>6} {'v2(p-1)':>8} {'p/n^2.5':>9}")
for n in ns:
    rs = [r for r in records if r['n']==n]
    if not rs: continue
    w = max(rs, key=lambda r:r['R'])
    P(f"{n:>5} {w['R']:8.4f} {w['B']:9.3f} {w['p']:>9} {w['m']:>8} {w['v2m']:>6} {v2(w['p']-1):>8} {w['shallow']:>9.2f}")

# ---- TOP 30 overall ----
records.sort(key=lambda r:-r['R'])
P("\n--- TOP 30 R overall (would-be refutations) ---")
P(f"{'R':>8} {'B':>9} {'p':>9} {'n':>5} {'m':>8} {'v2(m)':>6} {'v2(p-1)':>8} {'p/n^2.5':>9} {'2ord':>6}")
for r in records[:30]:
    o2 = '-'
    try:
        o2 = str(list(factorint((r['p']-1)).items()))
    except Exception: pass
    P(f"{r['R']:8.4f} {r['B']:9.3f} {r['p']:>9} {r['n']:>5} {r['m']:>8} {r['v2m']:>6} {v2(r['p']-1):>8} {r['shallow']:>9.2f}")

# ---- DEEP-band trend: does worst R grow with n at p/n^2.5 >= 8 ? ----
P("\n--- DEEP-BAND TREND (p/n^2.5 >= 8): worst & median R per n ---")
P("  (R GROWING with n here => conjecture in trouble)")
for n in ns:
    deep = [r for r in records if r['n']==n and r['shallow']>=8.0]
    if not deep:
        P(f"  n={n:>4}: (none)"); continue
    w = max(deep, key=lambda r:r['R'])
    Rs = sorted(r['R'] for r in deep)
    med = Rs[len(Rs)//2]
    P(f"  n={n:>4}: worstR={w['R']:.4f} (p={w['p']}, m={w['m']}, shallow={w['shallow']:.1f}); "
      f"medR={med:.4f}; max={Rs[-1]:.4f}; count={len(deep)}")

# ---- shallowness driver: bin worst R by p/n^2.5 band ----
P("\n--- SHALLOWNESS driver: worst R by p/n^2.5 band (all n) ---")
bands = [(0,2),(2,4),(4,8),(8,16),(16,64),(64,1e9)]
for lo,hi in bands:
    sel = [r for r in records if lo<=r['shallow']<hi]
    if not sel: continue
    w = max(sel, key=lambda r:r['R'])
    P(f"  p/n^2.5 in [{lo:>4},{hi:>6}): worstR={w['R']:.4f} (p={w['p']},n={w['n']},m={w['m']}); count={len(sel)}")

# ---- 2-adic driver in deep band ----
P("\n--- 2-ADIC driver (deep band p/n^2.5>=8): worst R by v2(m) ---")
deepall = [r for r in records if r['shallow']>=8.0]
for lab,cond in [("odd m (v2=0)", lambda r:r['v2m']==0),
                 ("v2(m)=1", lambda r:r['v2m']==1),
                 ("v2(m)=2", lambda r:r['v2m']==2),
                 ("v2(m)>=3", lambda r:r['v2m']>=3)]:
    sel = [r for r in deepall if cond(r)]
    if not sel: continue
    w = max(sel, key=lambda r:r['R'])
    P(f"  {lab:>14}: worstR={w['R']:.4f} (p={w['p']},n={w['n']},m={w['m']}); count={len(sel)}")

P("\nDONE.")
