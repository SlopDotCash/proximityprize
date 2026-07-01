# Focused r=3 calibration: reproduce in-tree DeepBandR3Bound.
#   #bad = n*C(n/4,2)+1 ; O_P(3)=C(n/4,2)=6,28 at n=16,32.
# Scan r=3 lines, report ALL lines achieving the target (and the max O_P over all lines).
from math import comb, gcd
from itertools import combinations
import sys
P1 = 2013265921
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def hser(elts,mmax,p):
    H=[0]*(mmax+1); H[0]=1
    for z in elts:
        for m in range(mmax,0,-1):
            H[m]=(H[m]+z*H[m-1])%p
    return H
def census(dom,n,p,r,e,f):
    a=r+1; ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1; mmax=max(ie,ie1,jf,jf1)
    fiber={}; gz=0; SonV=0
    for S in combinations(range(n),a):
        elts=[dom[i] for i in S]; H=hser(elts,mmax,p)
        he,he1,hf,hf1=H[ie],H[ie1],H[jf],H[jf1]
        if (he*hf1-hf*he1)%p==0:
            SonV+=1
            if hf%p!=0:
                g=(-he*pow(hf,p-2,p))%p
                if g==0: gz+=1
                fiber[g]=fiber.get(g,0)+1
    nd=sum(1 for g in fiber if g!=0)
    return SonV,nd,gz,fiber
def run(n):
    p=P1; r=3; dom=mu_n(n,p)
    tb=n*comb(n//4,2)+1; tOP=comb(n//4,2)
    bestOP=-1; bestline=None; hits=[]
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            if min(e-r,e-r+1,f-r,f-r+1)<0: continue
            SonV,nd,gz,fiber=census(dom,n,p,r,e,f)
            bad=nd+(1 if gz>0 else 0)
            d=gcd(abs(e-f),n); orbit=n//d; OP=nd//orbit if orbit else 0
            if bad==tb: hits.append((e,f,bad,SonV,OP,orbit))
            if OP>bestOP: bestOP=OP; bestline=(e,f,bad,SonV,OP,orbit)
    print(f"n={n}: target #bad={tb} O_P={tOP}")
    print(f"  #lines hitting target #bad={tb}: {len(hits)}; examples: {hits[:3]}")
    print(f"  MAX O_P over all lines = {bestOP} at line {bestline}; matches target O_P={tOP}? {bestOP==tOP}")
if __name__=="__main__":
    for n in [int(x) for x in sys.argv[1:]] or [16]:
        run(n)
