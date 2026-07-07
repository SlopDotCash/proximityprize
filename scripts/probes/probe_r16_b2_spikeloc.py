#!/usr/bin/env python3
"""R16 B2: locate the SECONDARY spikes that refute away-Wick (D = {0} u mu_n) at deg >= 4.

For failing cells, print the top off-D offsets s0 by |I(s0)| and classify them:
  - multiplicative order of s0 (is s0 in mu_{k n} for small k? in H?)
  - is s0 = y1 + y2 a sum of two mu_n elements? (additive doubling of the diagonal)
  - is s0 = y1 + y2 + y3? (triple sums)
  - is s0/(y1+y2) in mu_n for some pair? etc.
  - whether the top values are whole multiplicative mu_n-orbits or H-orbits.

Current key observation: in the counterexample n=64, deg=8, p=7681, the top off-D values are a
single mu_n-orbit with constant |I|=605.0, not isolated offsets.  The H-orbit containing it has
large variation, so the natural quotient for secondary-spike classification is by mu_n-cosets,
not by H-cosets.
Also: push beta toward 4 at deg in {4,8} to see if the failure persists at prize scaling.
"""
import numpy as np, math
from sympy import isprime

def factor(x):
    fs, d = set(), 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in factor(p-1)): return g

def mult_order_index(s, p, g):
    # return (p-1)/ord(s) = index of <s>; s = g^k, ord = (p-1)/gcd(k,p-1)
    # brute via baby steps is overkill; just compute ord directly
    o = 1; x = s % p
    while x != 1:
        x = x*s % p; o += 1
        if o > p: return None
    return o

def orbit(s, subgroup, p):
    return frozenset((s * u) % p for u in subgroup)

def run(p, n, deg, top=10):
    g = prim_root(p); m = (p-1)//n
    gm = pow(g, m, p); mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*gm % p
    munset = set(mun)
    ind = np.zeros(p, dtype=complex)
    for x in mun: ind[x] = 1
    eta = np.fft.ifft(ind)*p
    gd = pow(g, deg, p); Hsize = (p-1)//deg
    Hs = set(); x = 1
    for _ in range(Hsize): Hs.add(x); x = x*gd % p
    if not munset <= Hs:
        print(f"p={p} n={n} deg={deg}: SKIP"); return
    H = np.array(sorted(Hs))
    w = np.zeros(p, dtype=complex); w[H] = np.conj(eta[H])
    I = np.fft.ifft(w)*p; absI = np.abs(I)
    Sig = float(np.sum(np.abs(eta[H])**2))
    D = [0] + mun
    mask = np.ones(p, bool); mask[D] = False
    S2p = float(np.sum(absI[mask]**4))
    wickr = S2p/(3*p*Sig**2)
    # doubling sets
    sum2 = set((y1+y2) % p for y1 in mun for y2 in mun) - {0}
    print(f"p={p} n={n} deg={deg} |H|={Hsize} beta={math.log(p)/math.log(n):.2f} "
          f"S2'/Wick={wickr:.4f} {'FAIL' if wickr>1 else 'ok'}  sqrtSig={math.sqrt(Sig):.0f}")
    offs = [s for s in np.argsort(absI)[::-1] if mask[s]][:top]
    top_mu_orbits = {}
    top_H_orbits = {}
    for s in offs:
        o = mult_order_index(int(s), p, g)
        idx = (p-1)//o if o else None
        in2 = int(s) in sum2
        mu_orb = orbit(int(s), munset, p)
        H_orb = orbit(int(s), Hs, p)
        top_mu_orbits.setdefault(mu_orb, []).append(int(s))
        top_H_orbits.setdefault(H_orb, []).append(int(s))
        orb_vals = np.array([absI[t] for t in mu_orb])
        H_vals = np.array([absI[t] for t in H_orb])
        print(f"   s0={int(s):>7} |I|={absI[s]:8.1f} |I|/sqrtSig={absI[s]/math.sqrt(Sig):6.2f} "
              f"ord={o:>7} idx={idx:>5} inH={int(s) in Hs} in(mun+mun)={in2} "
              f"muOrb[min,max]=({orb_vals.min():.1f},{orb_vals.max():.1f}) "
              f"Horb[min,max]=({H_vals.min():.1f},{H_vals.max():.1f})")
    off_vals = absI[mask]
    q = np.quantile(off_vals, [0.5, 0.9, 0.99, 0.999])
    mu_orb_count = len(top_mu_orbits)
    H_orb_count = len(top_H_orbits)
    print(f"   top{top}: mu_n-orbits={mu_orb_count}, H-orbits={H_orb_count}, "
          f"off-|I| quantiles 50/90/99/99.9%={[round(float(x),1) for x in q]}")

def primes_1mod(m, count, start):
    out, x = [], max(start - start % m + 1, m + 1)
    while len(out) < count and x < 17_000_000:
        if isprime(x): out.append(x)
        x += m
    return out

# failing cells from spikedom probe
for (p, n, deg) in [(7681,64,8),(193,8,8),(641,8,4),(1153,32,4),(4481,16,4),(262657,64,8)]:
    run(p, n, deg)

print("\n=== beta -> 4 persistence, deg in {4,8} ===")
for n in (16, 32):
    for deg in (4, 8):
        for p in primes_1mod(n*deg, 3, n**4):
            g = prim_root(p)
            run(p, n, deg, top=4)
