#!/usr/bin/env python3
"""Confirm V (the bad-subset set) is dilation-invariant: the set of bad S is closed under
   S->gS (shift indices by 1 mod n), so #S_on_V = sum of dilation-orbit sizes. Report the
   orbit-size distribution of the bad-SUBSET set (n=16,32). Also confirm gamma(gS)=g^{e-f}gamma(S)."""
from math import comb, gcd
from itertools import combinations
from collections import Counter
p=2013265921
def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def h_upto(Sv,M):
    h=[0]*(M+1); h[0]=1
    for z in Sv:
        new=[0]*(M+1); prev=0
        for m in range(M+1): prev=(h[m]+z*prev)%p; new[m]=prev
        h=new
    return h
def go(n,e,f,r):
    a0=r+1; dom=mu_n(n); M=max(e-r,e-r+1,f-r,f-r+1,0)
    badS=set()
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1,hfr,hfr1=H(e-r),H(e-r+1),H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%p!=0: continue
        if hfr==0: continue
        badS.add(S)
    # orbit structure under shift S->{(i+1)%n}
    def shift(S): return tuple(sorted((i+1)%n for i in S))
    seen=set(); orbsizes=[]
    for S in badS:
        if S in seen: continue
        orb=set(); cur=S
        while cur not in orb:
            orb.add(cur); cur=shift(cur)
        # only count if whole orbit is in badS (it must be, by invariance) — verify
        assert orb<=badS, f"orbit not contained! S={S}"
        seen|=orb; orbsizes.append(len(orb))
    dist=dict(sorted(Counter(orbsizes).items()))
    print(f"n={n} r={r} line(x^{e},x^{f}): #S_on_V={len(badS)}  dilation-orbit-size dist {{size:#orbits}} = {dist}")
    print(f"   all orbits sizes divide n={n}? {all(n%s==0 for s in orbsizes)}  #orbits={len(orbsizes)}")
    print(f"   sum check: {sum(s for s in orbsizes)} == {len(badS)} ? {sum(orbsizes)==len(badS)}")
if __name__=="__main__":
    go(16,9,15,5)
    go(32,17,31,5)
