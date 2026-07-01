"""
probe_444_mech1_globalsame.py -- FAST: per (r,n), global O_P-max vs same-parity O_P-max and the
WINNING parity classes (is the maximizer same-parity? does same-parity achieve the global max?).
Numpy-free, builds H-table once. Two primes.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import defaultdict

PRIMES=[2013265921,3221225473]
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
    w=gen(n,p); a0=r+1
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n,p) for S in subs]
    res={}  # (e,f)->O_P
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            if max(e-r+1,f-r+1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d; cos=set()
            for H in Hc:
                if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
                if H[f-r]==0: continue
                g=(-H[e-r]*pow(H[f-r],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            res[(e,f)]=len(cos)
    gmax=max(res.values())
    smax=max(v for (e,f),v in res.items() if (e-f)%2==0)
    gmax_lines=[(e,f) for (e,f),v in res.items() if v==gmax]
    gmax_parities=set(((e-f)%2) for (e,f) in gmax_lines)  # 0=same,1=opp
    return gmax,smax,gmax_lines[:4],gmax_parities,comb(n//2,r-1)

if __name__=="__main__":
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for p in PRIMES:
        print(f"### p={p}")
        for (r,n) in todo:
            gmax,smax,lines,par,bnd=scan(n,r,p)
            same_achieves = (smax==gmax)
            par_str = {0:'SAME',1:'OPP'}
            pars=sorted(par_str[x] for x in par)
            print(f"  r={r} n={n}: globalO_P={gmax} sameparO_P={smax} -> same achieves global? {same_achieves}; "
                  f"global-max parity classes={pars}; bound C(n/2,r-1)={bnd} ratio={gmax/bnd:.3f}; egLines={lines}")
