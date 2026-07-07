"""
probe_444_angleC_worstline.py -- characterize the O_P/(K d/n) WORST line family and find a clean
crude bound formula for O_P that PROVABLY clears K*d/n.

From the full-line scan:
  worst RATIO lines are d=1 lines (e.g. n=16 r=3 (15,8); n=32 r=3 (31,16) i.e. (n-1, n/2)).
  We tabulate O_P for these worst lines across n and r, and across SEVERAL structured line
  families, to identify the governing O_P formula and a provable crude bound.

We compute O_P exactly for a chosen line and ALSO break O_P down by:
  - whether the bad gammas are roots of unity (gamma^? = const)
  - the gap-structure / antipodal type of the bad-S orbit reps
"""
import sys
from math import comb, gcd, factorial
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def OP_detailed(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d; mult=pow(w,(e-f)%n,p)
    nz=set()
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
        if (her*hfr1-hfr*her1)%p: continue
        if hfr==0: continue
        g=(-her*pow(hfr,p-2,p))%p
        if g: nz.add(g)
    # orbit reps
    rem=set(nz); reps=[]
    while rem:
        x=next(iter(rem)); o=set(); cur=x
        for _ in range(n): o.add(cur); cur=cur*mult%p
        reps.append(x); rem-=o
    OP=len(reps)
    return OP,nz,reps,d,nd

if __name__=="__main__":
    print("worst-ratio line family (n-1, n/2)  [d=1] across n,r:")
    print(f"{'r':>2}{'n':>4}{'O_P':>6}{'C(n/2,r-1)':>11}{'C(n/4,r-1)':>11}{'C(n/2,2)':>9}{'r*n/4':>7}{'K*d/n':>9}")
    for r in [3,4,5]:
        for n in [16,32]:
            e,f=n-1,n//2
            if e-r<0 or f-r<0: continue
            OP,nz,reps,d,nd=OP_detailed(n,r,e,f)
            K=(1<<r)*comb(n//2,r)
            print(f"{r:>2}{n:>4}{OP:>6}{comb(n//2,r-1):>11}{comb(n//4,r-1) if n//4>=r-1 else 0:>11}"
                  f"{comb(n//2,2):>9}{r*n//4:>7}{K*d/n:>9.0f}")
