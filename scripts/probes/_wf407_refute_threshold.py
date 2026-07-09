#!/usr/bin/env python3
"""
#407 REFUTATION pt4 — the WORST-CASE locus is near-threshold p ~ c*n^2.5.
The growth probe showed spikes (R up to 2.06) cluster at small shallow=p/n^2.5.
The decisive refutation question: along the near-threshold ridge (the LOCUS of
worst R), does the peak R GROW with n, or is it CAPPED?

For each n=2^mu we scan ALL primes p in a window around the threshold
[c_lo*n^2.5, c_hi*n^2.5] (small shallow, where spikes live) and at SEVERAL
shallow targets, recording the worst R. We push n as far as exact compute allows.
We also report the worst over a WIDE shallow window to be sure we caught the ridge.
"""
import math
import numpy as np
from sympy import isprime, primitive_root

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
    return best

P("="*78)
P("REFUTATION pt4 — worst R along the near-threshold ridge, growing n")
P("="*78)
P("  scanning ALL primes p=n*m+1 with shallow=p/n^2.5 in [0.3, 6], per n=2^mu")
P("  (this is the LOCUS where spikes were observed); does peak R grow with n?")

ns = [8,16,32,64,128,256,512,1024,2048]
SH_LO, SH_HI = 0.3, 6.0
PCAP = 9_000_000

P(f"\n  {'n':>6} {'peakR':>8} {'B':>10} {'p':>9} {'m':>7} {'shallow':>8} {'#scan':>6} {'p99R':>7}")
results=[]
for n in ns:
    mlo = max(2, int(SH_LO * n**2.5 / n))
    mhi = int(SH_HI * n**2.5 / n)
    Rs=[]; best=None; cnt=0
    for m in range(mlo, mhi+1):
        p = n*m+1
        if p > PCAP: break
        if not isprime(p): continue
        g = primitive_root(p)
        B = floor_B(p, n, g)
        R = B/math.sqrt(n*math.log(m))
        Rs.append(R); cnt+=1
        if best is None or R>best[0]:
            best=(R,B,p,m,p/n**2.5)
    if not Rs:
        P(f"  {n:>6}  (none / p too large)"); continue
    Rs.sort()
    p99 = Rs[min(len(Rs)-1, int(0.99*len(Rs)))]
    R,B,p,m,sh = best
    results.append((n,R,sh,p,m))
    P(f"  {n:>6} {R:8.4f} {B:>10.3f} {p:>9} {m:>7} {sh:>8.3f} {cnt:>6} {p99:>7.4f}")

P("\n--- peak-R trend with n along the ridge ---")
if len(results)>=2:
    P(f"  n:    " + " ".join(f"{n:>7}" for n,_,_,_,_ in results))
    P(f"  peakR:" + " ".join(f"{R:7.3f}" for _,R,_,_,_ in results))
    # linear fit of peakR vs log2(n)
    xs = np.array([math.log2(n) for n,_,_,_,_ in results])
    ys = np.array([R for _,R,_,_,_ in results])
    A = np.vstack([xs, np.ones_like(xs)]).T
    slope, intercept = np.linalg.lstsq(A, ys, rcond=None)[0]
    P(f"  linear fit peakR ~ {slope:.4f}*log2(n) + {intercept:.4f}")
    P(f"  => per-doubling-of-n change in peakR: {slope:.4f}")
    if slope > 0.05:
        P("  >>> peakR TRENDS UP with n: potential refutation signal (verify breadth).")
    else:
        P("  >>> peakR FLAT/declining: floor supported (spike is a bounded artifact).")

P("\nDONE pt4.")
