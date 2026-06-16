#!/usr/bin/env python3
"""
#407 REFUTATION pt5 — FAST high-n peak test, narrow shallow window [1.3,3.0]
(where the Fermat-prime spike R=2.07 lives, shallow=2.0). Pushes n up to 4096
with a NARROW window so compute stays bounded. Decisive: does the near-threshold
peak R grow with n, or stay capped ~2.0?  Also records the v2(m) and oddpart(m)
of the worst prime to see if the maximizer keeps the 'big 2-power + small odd' shape.
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

def oddpart(x):
    while x%2==0: x//=2
    return x

P("="*78)
P("REFUTATION pt5 — FAST high-n peak, narrow shallow [1.3,3.0]")
P("="*78)
SH_LO, SH_HI = 1.3, 3.0
ns = [16,32,64,128,256,512,1024,2048,4096]
P(f"  {'n':>6} {'peakR':>8} {'B':>10} {'p':>10} {'m':>7} {'oddp(m)':>8} {'v2(m)':>6} {'shallow':>8} {'#scan':>6}")
res=[]
for n in ns:
    mlo = max(2, int(SH_LO*n**1.5))
    mhi = int(SH_HI*n**1.5)
    if n*mhi > 12_000_000:
        mhi = 12_000_000//n
    best=None; cnt=0
    for m in range(mlo, mhi+1):
        p=n*m+1
        if not isprime(p): continue
        g=primitive_root(p)
        B=floor_B(p,n,g)
        R=B/math.sqrt(n*math.log(m))
        cnt+=1
        if best is None or R>best[0]:
            best=(R,B,p,m,oddpart(m),(m&-m).bit_length()-1,p/n**2.5)
    if best is None:
        P(f"  {n:>6}  (none)"); continue
    R,B,p,m,op,v,sh=best
    res.append((n,R))
    P(f"  {n:>6} {R:8.4f} {B:>10.3f} {p:>10} {m:>7} {op:>8} {v:>6} {sh:>8.3f} {cnt:>6}")

P("\n--- peak-R vs n ---")
P("  n:    " + " ".join(f"{n:>6}" for n,_ in res))
P("  peakR:" + " ".join(f"{R:6.3f}" for _,R in res))
if len(res)>=3:
    xs=np.array([math.log2(n) for n,_ in res]); ys=np.array([R for _,R in res])
    A=np.vstack([xs,np.ones_like(xs)]).T
    sl,ic=np.linalg.lstsq(A,ys,rcond=None)[0]
    P(f"  fit peakR ~ {sl:.4f}*log2(n)+{ic:.4f}  (per-doubling slope {sl:.4f})")
    P("  >>> "+("UP-TREND: refutation signal" if sl>0.05 else "FLAT/CAPPED: floor supported"))
P("\nDONE pt5.")
