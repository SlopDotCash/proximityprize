#!/usr/bin/env python3
"""
[centrallaw] DEEP push of FAMILY A (fixed index) to large n, plus:
 - separate odd-n vs 2-power-n (Fermat-like) behavior (KB: 2-power antipodal inflates B),
 - careful estimate of the constant C = R, and of C2 = R via sqrt(2 n ln m) (Salem-Zygmund),
 - test alternative normalizations to confirm sqrt(n ln m) is the RIGHT one:
     R1 = B/sqrt(n)          (should GROW like sqrt(ln m) -> grows slowly with m, flat in n at fixed m)
     R2 = B/sqrt(n ln m)     (the conjecture: should be FLAT)
     R3 = B/sqrt(n ln p)     (alternative: ln p vs ln m, distinguishes regimes)
Large p: O(p) per prime, fine up to p~3e5 quickly; we go to a few 1e5.
"""
import numpy as np, math
from sympy import isprime, primitive_root

def floor(p, n):
    m = (p-1)//n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64); cur=1
    for k in range(n): mu[k]=cur; cur=(cur*gm)%p
    tp = 2.0*math.pi/p; best=0.0; r=1
    for _ in range(m):
        pr=(r*mu)%p
        s=np.cos(tp*pr).sum()+1j*np.sin(tp*pr).sum()
        a=abs(s)
        if a>best: best=a
        r=(r*g)%p
    return best, m

def is2power(n):
    return n & (n-1) == 0

# Fixed-index family at m_target=16, pushing n large, recording parity of n.
print("FAMILY A deep (m_target~16). Distinguish n=2-power (Fermat-like) from generic n.")
print(f"{'n':>6} {'p':>9} {'m':>5} {'2pow':>4} {'B':>10} {'R2=B/sqrt(n lnm)':>16} {'R3=B/sqrt(n lnp)':>16}")
ns = [16,32,64,96,128,160,192,256,320,384,512,640,768,896,1024,1280,1536,2048,2560,3072,4096,5120,6144,8192]
rows=[]
for n in ns:
    res=None
    for m in [16,17,15,18,14,19,13,20,21,22,23,24,12,11,25,26]:
        if m<3: continue
        c=n*m+1
        if isprime(c): res=(c,m); break
    if res is None: continue
    p,m=res
    if p>1_200_000: continue
    B,mm=floor(p,n)
    R2=B/math.sqrt(n*math.log(m))
    R3=B/math.sqrt(n*math.log(p))
    rows.append((n,p,m,is2power(n),B,R2,R3))
    print(f"{n:>6} {p:>9} {m:>5} {str(is2power(n)):>4} {B:>10.4f} {R2:>16.4f} {R3:>16.4f}")

odd_R2=[r[5] for r in rows if not r[3]]
pow_R2=[r[5] for r in rows if r[3]]
allR2=[r[5] for r in rows]
allR3=[r[6] for r in rows]
ns_r=[r[0] for r in rows]
print()
print(f"ALL R2: n={len(allR2)} mean={np.mean(allR2):.4f} std={np.std(allR2):.4f} "
      f"max={max(allR2):.4f} min={min(allR2):.4f}")
print(f"   trend dR2/dln(n) = {np.polyfit(np.log(ns_r),allR2,1)[0]:+.5f}")
print(f"generic-n  R2: mean={np.mean(odd_R2):.4f} std={np.std(odd_R2):.4f} max={max(odd_R2):.4f}")
print(f"2-power-n  R2: mean={np.mean(pow_R2):.4f} std={np.std(pow_R2):.4f} max={max(pow_R2):.4f}")
print(f"ALL R3 (ln p norm): mean={np.mean(allR3):.4f} std={np.std(allR3):.4f}  "
      f"trend dR3/dln(n)={np.polyfit(np.log(ns_r),allR3,1)[0]:+.5f}")
print()
print("INTERPRETATION:")
print(" - R2 flat (slope~0) and bounded ~[1,1.5] => sqrt(n ln m) is the correct normalization.")
print(" - If R3 (ln p norm) DRIFTS while R2 flat => ln m (not ln p) is load-bearing => prize form correct.")
print(" - If 2-power-n R2 noticeably > generic-n R2 => the worst case is 2-power (antipodal) inflation.")
