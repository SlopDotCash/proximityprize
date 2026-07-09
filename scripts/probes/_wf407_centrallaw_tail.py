#!/usr/bin/env python3
"""[centrallaw] FAST tail/sup scan for the prize constant C (cap 20000, vectorized)."""
import numpy as np, math, sys
from sympy import isprime, primitive_root

def floor(p, n):
    m=(p-1)//n; g=primitive_root(p); gm=pow(g,m,p)
    mu=np.empty(n,dtype=np.int64); cur=1
    for k in range(n): mu[k]=cur; cur=(cur*gm)%p
    tp=2.0*math.pi/p; best=0.0; r=1
    for _ in range(m):
        pr=(r*mu)%p
        s=np.cos(tp*pr).sum()+1j*np.sin(tp*pr).sum()
        a=abs(s)
        if a>best: best=a
        r=(r*g)%p
    return best,m

PCAP=20000
records=[]
for n in range(4, 260):
    for m in range(4, 400):
        p=n*m+1
        if p>PCAP: break
        if not isprime(p): continue
        B,_=floor(p,n)
        lnm=math.log(m)
        R2=B/math.sqrt(n*lnm)
        records.append((R2,n,p,m))
records.sort(reverse=True)
allR2=np.array([r[0] for r in records])
print(f"scanned {len(records)} triples p<{PCAP}")
print("TOP 15 by R2:")
for R2,n,p,m in records[:15]:
    print(f"  R2={R2:.4f}  n={n} p={p} m={m}")
print(f"sup R2={allR2.max():.4f}  99pct={np.percentile(allR2,99):.4f}  mean={allR2.mean():.4f}  median={np.median(allR2):.4f}")
print(f"frac>1.5={np.mean(allR2>1.5):.4f} frac>1.6={np.mean(allR2>1.6):.4f} frac>1.7={np.mean(allR2>1.7):.4f}")
lp=np.array([math.log2(r[2]) for r in records])
print("sup R2 per log2(p) bucket (tail creep test):")
for lo in range(7,15):
    mask=(lp>=lo)&(lp<lo+1)
    if mask.sum()>0:
        print(f"  log2 p in [{lo},{lo+1}): n={mask.sum():4d} supR2={allR2[mask].max():.4f} mean={allR2[mask].mean():.4f}")
mm=np.array([r[3] for r in records])
print("sup R2 per m bucket:")
for lo,hi in [(4,8),(8,16),(16,32),(32,64),(64,128),(128,400)]:
    mask=(mm>=lo)&(mm<hi)
    if mask.sum()>0:
        print(f"  m in [{lo},{hi}): n={mask.sum():4d} supR2={allR2[mask].max():.4f} mean={allR2[mask].mean():.4f}")
