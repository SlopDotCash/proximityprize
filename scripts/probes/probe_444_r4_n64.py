# r=4 maximizer (x^{n/2+2},x^{n/4+1}) at n=64. Expect O_P=897.
# Optimized: precompute power table; iterate combos of indices; fiber via dict.
from math import comb, gcd
from itertools import combinations
from collections import Counter
import sys
P1=2013265921
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def main():
    n=64; p=P1; r=4; a=r+1
    e=n//2+2; f=n//4+1            # (34,17)
    ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1   # 30,31,13,14
    mmax=max(ie,ie1,jf,jf1)
    dom=mu_n(n,p)
    # we only need H[ie],H[ie1],H[jf],H[jf1]; track just these 4 via the same forward recurrence,
    # but it's cheaper to compute the full truncated series to mmax (=31). a=5 elements.
    SonV=0; fiber={}; gz=0; inf_ct=0; invcache={}
    cnt=0
    for S in combinations(range(n),a):
        H0=H1=Hf0=Hf1=0
        # forward series to mmax
        H=[0]*(mmax+1); H[0]=1
        for i in S:
            z=dom[i]
            for m in range(1,mmax+1):
                H[m]=(H[m]+z*H[m-1])%p
        he,he1,hf,hf1=H[ie],H[ie1],H[jf],H[jf1]
        if (he*hf1-hf*he1)%p==0:
            SonV+=1
            if hf%p==0:
                inf_ct+=1
            else:
                inv=invcache.get(hf)
                if inv is None: inv=pow(hf,p-2,p); invcache[hf]=inv
                g=(-he*inv)%p
                if g==0: gz+=1
                fiber[g]=fiber.get(g,0)+1
        cnt+=1
        if cnt % 500000 == 0:
            print(f"  ...{cnt} subsets, SonV={SonV} so far", flush=True)
    nz=sum(1 for g in fiber if g!=0)
    d=gcd(abs(e-f),n); orbit=n//d; OP=nz//orbit if orbit else 0
    K=(1<<r)*comb(n//2,r)
    has_zero=1 if gz>0 else 0
    bad=nz+has_zero
    szc=Counter(c for g,c in fiber.items() if g!=0)
    print(f"n={n} line(x^{e},x^{f}): S_on_V={SonV} #bad(distinct gamma)={bad} K={K}")
    print(f"  S_on_V<=K? {SonV<=K} bad<=S_on_V? {bad<=SonV} bad<=K? {bad<=K}")
    print(f"  ratios S_on_V/K={SonV/K:.5f} bad/K={bad/K:.5f} bad/S_on_V={bad/SonV:.5f}")
    print(f"  nz_gamma={nz} gamma_zero={has_zero} inf_pins={inf_ct} d={d} orbit={orbit} O_P={OP} (expect 897)")
    print(f"  fiber-size dist (size->#gamma): {dict(sorted(szc.items()))}")
main()
