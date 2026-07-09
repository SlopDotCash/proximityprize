"""
probe_444_angleC_crudecheck.py -- STRESS-TEST the candidate crude bound  O_P <= C(n/2, r-1)
across EVERY admissible line (the prize statement must hold for every witness), and report the
worst (max) O_P / C(n/2,r-1) ratio.  Two primes for char-0 confirmation.

If O_P <= C(n/2,r-1) for all lines, then via the analytic clearance
   C(n/2,r-1) <= K*d/n   (proven for n>=~2r, all r)
we get O_P <= K*d/n => #bad=(n/d)O_P <= K => CensusDomination supply bound.
"""
import sys
from math import comb, gcd
from itertools import combinations

def gen(n,p):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def scan(n,r,p):
    w=gen(n,p); a0=r+1; Hmax=n
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],Hmax,p) for S in subs]
    bound=comb(n//2,r-1) if n//2>=r-1 else 0
    worst=(0.0,None,0,0)  # ratio, line, OP, d
    nlines=0; allok=True
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            er,fr,er1,fr1=e-r,f-r,e-r+1,f-r+1
            if max(er1,fr1)>Hmax: continue
            d=gcd((e-f)%n,n); nd=n//d
            cos=set()
            for H in Hc:
                if (H[er]*H[fr1]-H[fr]*H[er1])%p: continue
                if H[fr]==0: continue
                g=(-H[er]*pow(H[fr],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            OP=len(cos); nlines+=1
            if OP>bound: allok=False
            ratio=OP/bound if bound else float('inf')
            if ratio>worst[0]: worst=(ratio,(e,f),OP,d)
    return bound,worst,nlines,allok

if __name__=="__main__":
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for p in [2013265921, 3221225473]:
        print(f"### prime p={p}")
        for (r,n) in todo:
            bound,worst,nlines,allok=scan(n,r,p)
            print(f"  r={r} n={n}: C(n/2,r-1)={bound}  scanned {nlines} lines  "
                  f"max O_P/bound={worst[0]:.3f} at line {worst[1]} O_P={worst[2]} d={worst[3]}  "
                  f"ALL O_P<=C(n/2,r-1)? {allok}")
