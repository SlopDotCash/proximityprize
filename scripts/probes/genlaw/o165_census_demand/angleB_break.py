# LOAD-BEARING TEST: at the r=6 n=32 line (x^20,x^16) where the crude chain #bad<=#{S on V}<=K
# DIED (#{S on V}=537600 > K=512512), does ANGLE B survive? I.e. is #distinct nonzero gamma <= K,
# and is there a bounded-to-one map into signed r-subsets? We only need #gamma (cheap-ish with
# numpy h_m over all C(32,7)=3.4M subsets is heavy; instead enumerate with a vectorized h_m).
#
# We compute h_m for all (r+1)-subsets via numpy by iterating subsets in chunks. To keep it
# tractable we use the DILATION ORBIT structure: bad set is a union of mu_n-dilation orbits, so we
# enumerate orbit REPRESENTATIVES (subsets containing index 0 up to rotation) — reduces by ~n.
# Even so 3.4M/32 ~ 107k reps * h_m is fine in Python.
from math import comb, gcd
from itertools import combinations
from collections import Counter
import sys
p = 2013265921
def inv(x): return pow(x,p-2,p)
def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
    raise RuntimeError
def h_ps(elts,mmax):
    L=len(elts);P=[L%p]+[0]*mmax;cur=[1]*L
    for i in range(1,mmax+1):
        s=0
        for j in range(L): cur[j]=(cur[j]*elts[j])%p; s+=cur[j]
        P[i]=s%p
    H=[1]+[0]*mmax
    for m in range(1,mmax+1):
        acc=0
        for i in range(1,m+1): acc=(acc+P[i]*H[m-i])%p
        H[m]=(acc*inv(m))%p
    return H

def count_gamma_orbitreps(n,r,e,f):
    """Enumerate subsets containing index 0 (orbit reps under cyclic dilation by w => index +1 mod n).
       Each bad subset's dilation orbit has size n/stab; gamma orbit size n/d. We recover total #gamma
       by collecting actual gamma values from reps and CLOSING under gamma -> gamma * w^{(e-f)k}."""
    dom=mu_n(n); a=r+1
    me,mf,me1,mf1=e-r,f-r,e-r+1,f-r+1
    mmax=max(me,mf,me1,mf1)
    w=dom[1]
    shift=pow(w,(e-f)%n,p)  # gamma multiplier per +1 dilation
    gammas=set(); reps=0
    # subsets containing 0: choose remaining r from 1..n-1
    for rest in combinations(range(1,n),r):
        S=(0,)+rest
        elts=[dom[i] for i in S]; H=h_ps(elts,mmax)
        he,hf,he1,hf1=H[me],H[mf],H[me1],H[mf1]
        if (he*hf1-hf*he1)%p: continue
        if hf%p==0: continue
        g=(-he*inv(hf))%p
        if g==0: continue
        reps+=1
        # add full dilation orbit of gamma
        cur=g
        for _ in range(n):
            gammas.add(cur); cur=(cur*shift)%p
    return gammas,reps

if __name__=="__main__":
    n,r,e,f = 32,6,20,16
    K=(1<<r)*comb(n//2,r)
    print(f"Computing #gamma for n={n} r={r} line(x^{e},x^{f}) [the crude-chain BREAK line]...", flush=True)
    gammas,reps=count_gamma_orbitreps(n,r,e,f)
    print(f"  reps(containing 0)={reps}  #distinct nonzero gamma(orbit-closed)={len(gammas)}", flush=True)
    print(f"  K=2^{r} C({n//2},{r})={K}  bad/K={len(gammas)/K:.5f}  bad<=K? {len(gammas)<=K}", flush=True)
