#!/usr/bin/env python3
"""
[centrallaw] WORST-CASE / TAIL search for the constant C in B <= C sqrt(n ln m).
Scan MANY primes per (n-band, m-band) and record the SUP of R2 over all of them.
The prize is an UPPER bound, so what matters is sup R2, not mean. We want to know:
 (1) does sup R2 stay bounded as n,m grow (no divergence) ?
 (2) what is the empirical C (sup) and does it creep up?
We scan, for each n in a grid, ALL valid m in [4, m_max] giving prime p=n*m+1 below a cap,
and track the running max R2 with the (n,p,m) achieving it.
"""
import numpy as np, math
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

PCAP=60000
records=[]   # (R2, n, p, m, R1)
for n in range(6, 400):
    for m in range(4, 600):
        p=n*m+1
        if p>PCAP: break
        if not isprime(p): continue
        if math.gcd(n,m)!=0:  # always true; placeholder
            pass
        B,_=floor(p,n)
        lnm=math.log(m)
        if lnm<=0: continue
        R2=B/math.sqrt(n*lnm)
        records.append((R2,n,p,m,B/math.sqrt(n)))

records.sort(reverse=True)
print(f"scanned {len(records)} (n,p,m) triples, all primes p<{PCAP}.")
print()
print("TOP 20 by R2=B/sqrt(n ln m)  (these constrain the prize constant C):")
print(f"{'R2':>8} {'n':>6} {'p':>8} {'m':>6} {'B':>10} {'lnm':>6}")
for R2,n,p,m,R1 in records[:20]:
    print(f"{R2:>8.4f} {n:>6} {p:>8} {m:>6} {R1*math.sqrt(n):>10.4f} {math.log(m):>6.3f}")

allR2=np.array([r[0] for r in records])
print()
print(f"sup R2 = {allR2.max():.4f}   (empirical upper-bound constant C)")
print(f"99th pct R2 = {np.percentile(allR2,99):.4f}")
print(f"mean R2 = {allR2.mean():.4f}   median = {np.median(allR2):.4f}")
print(f"frac R2>1.5 = {np.mean(allR2>1.5):.4f}   frac R2>1.6 = {np.mean(allR2>1.6):.4f}  frac R2>1.7={np.mean(allR2>1.7):.4f}")

# Does sup R2 over a window grow with p? Bucket by log(p) and report per-bucket max.
print()
print("sup R2 per log2(p) bucket (does the tail creep UP with p?):")
lp=np.array([math.log2(r[2]) for r in records])
for lo in range(7, 17):
    mask=(lp>=lo)&(lp<lo+1)
    if mask.sum()>0:
        print(f"  log2 p in [{lo},{lo+1}): count={mask.sum():4d}  sup R2={allR2[mask].max():.4f}  mean={allR2[mask].mean():.4f}")
# also sup per small-m (m small => fewer phases => potentially larger relative fluctuation)
print()
print("sup R2 per m bucket (small m = few Gauss phases):")
mm=np.array([r[3] for r in records])
for lo,hi in [(4,8),(8,16),(16,32),(32,64),(64,128),(128,256),(256,600)]:
    mask=(mm>=lo)&(mm<hi)
    if mask.sum()>0:
        print(f"  m in [{lo},{hi}): count={mask.sum():4d}  sup R2={allR2[mask].max():.4f}  mean={allR2[mask].mean():.4f}")
