"""
Decisive test for Angle A feasibility. A polynomial-method / Schwartz-Zippel bound on
#{S subset mu_n : s_lambda(S)=0} would give density ~ deg/|field| or ~ (per the
combinatorial-nullstellensatz on the n-point grid) something like |lambda|/n * C(n,r+1)
in the BEST case. We test the ACTUAL density of Schur-vanishing against:
  (a) generic codim-1 over mu_n: expect ~ C(n,r+1)/n
  (b) "degree bound": fraction <= |lambda| * (something)
across MANY admissible lines to see the worst-case density and whether ANY bound of the
form  c * C(n,r+1)  with c<= K/C(n,r+1)~0.15 can hold for the GENERIC-pinned part.
We sweep all admissible lines for r=4,5,6 at n=32 and report max generic-density.
"""
from math import comb, gcd
from itertools import combinations
p=2013265921
def mu_n(n,P=p):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return [pow(h,i,P) for i in range(n)]
def h_upto(Sv,M,P=p):
    h=[0]*(M+1); h[0]=1
    for z in Sv:
        new=[0]*(M+1); prev=0
        for m in range(M+1): prev=(h[m]+z*prev)%P; new[m]=prev
        h=new
    return h
def counts(n,e,f,r,P=p):
    a0=r+1; dom=mu_n(n,P); M=max(e-r,e-r+1,f-r,f-r+1,0)
    tot=0; gen=0
    # precompute all h-vectors once is too heavy; just stream
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M,P)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1,hfr,hfr1=H(e-r),H(e-r+1),H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%P!=0: continue
        tot+=1
        if hfr!=0 and her!=0: gen+=1
    return tot,gen
n=32
C=comb(n,0)  # placeholder
import sys
print(f"n={n}: sweeping admissible lines, reporting #SonV(total), generic, K, ratios")
for r in [4,5,6]:
    a0=r+1; K=(1<<r)*comb(n//2,r); Cn=comb(n,a0)
    best=None
    # admissible: e>=r (so e-r>=0), f>=r (f-r>=0), e!=f, e,f in [r, n-1] roughly. Sweep a manageable grid.
    cand=[]
    for e in range(r, n):
        for f in range(r, n):
            if e==f: continue
            cand.append((e,f))
    # too many; just test the worst region near e~3n/4..n, f below. Subsample structured ones.
    test_lines=[(e,f) for (e,f) in cand if abs(e-f) in (1,2,3,4) and e>=n//2]
    worst_tot=0; worst_gen=0; wl=None
    for (e,f) in test_lines:
        tot,gen=counts(n,e,f,r)
        if gen>worst_gen: worst_gen=gen; worst_tot=tot; wl=(e,f)
    print(f" r={r}: worst line {wl} K={K} C={Cn} worst_tot={worst_tot} ({worst_tot/K:.3f}K) worst_gen={worst_gen} ({worst_gen/K:.3f}K, {worst_gen/Cn:.4f}C)  C/n={Cn/n:.0f}")
