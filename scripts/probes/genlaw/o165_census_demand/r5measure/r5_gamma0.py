#!/usr/bin/env python3
"""Confirm gamma=0 IS the giant-fiber value, and report #S_on_V split into gamma=0 vs gamma!=0,
   to see whether the gamma!=0 part of the variety stays far below K (robustness of crude chain).
   Also report V's effective 'degree' diagnostics: how many S satisfy V vs ambient C(n,a0)."""
from math import comb, gcd
from itertools import combinations
from collections import Counter
import sys
p = 2013265921
def mu_n(n, prime):
    e=(prime-1)//n
    for c in range(2,400):
        h=pow(c,e,prime)
        if pow(h,n,prime)==1 and pow(h,n//2,prime)!=1: return [pow(h,i,prime) for i in range(n)]
def h_upto(Sv,M,prime):
    h=[0]*(M+1); h[0]=1
    for z in Sv:
        new=[0]*(M+1); prev=0
        for m in range(M+1):
            prev=(h[m]+z*prev)%prime; new[m]=prev
        h=new
    return h
def go(n,e,f,r,prime):
    a0=r+1; dom=mu_n(n,prime)
    idxs=[e-r,e-r+1,f-r,f-r+1]; M=max(idxs+[0])
    K=(1<<r)*comb(n//2,r); ambient=comb(n,a0)
    g0_fiber=0; nonzero_S=0; gammas=Counter()
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M,prime)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1=H(e-r),H(e-r+1); hfr,hfr1=H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%prime!=0: continue
        if hfr==0: continue
        gam=(-her*pow(hfr,prime-2,prime))%prime
        gammas[gam]+=1
        if gam==0: g0_fiber+=1
        else: nonzero_S+=1
    S_on_V=g0_fiber+nonzero_S
    print(f"n={n} line(x^{e},x^{f}) r={r}: ambient C(n,a0)={ambient}")
    print(f"  #S_on_V={S_on_V}  = gamma0_fiber({g0_fiber}) + gamma!=0 S({nonzero_S})")
    print(f"  K={K}  #S_on_V/K={S_on_V/K:.4f}  gamma!=0 part /K = {nonzero_S/K:.4f}")
    print(f"  V density #S_on_V/ambient = {S_on_V/ambient:.5f}  (vs 1/n={1/n:.5f}; codim-1 heuristic ~1/n)")
    print(f"  gamma0 IS the max fiber? {gammas[0]==max(gammas.values())}  (gamma0 fiber={gammas[0]}, max={max(gammas.values())})")
if __name__=="__main__":
    ns=[int(x) for x in sys.argv[1:]] if len(sys.argv)>1 else [16,32]
    for n in ns:
        go(n,n//2+1,n-1,5,p)
