"""
Angle A structural probe. V = {S subset mu_n, |S|=r+1 : s_lambda(S)=0}, lambda=(e-r,f-r+1) 2-row.
GOAL: understand WHY #{S on V}/C(n,r+1) ~ 0.1-0.16 (fat), not 1/n, and find a provable bound.

Key fact (Schur on roots of unity): for S a (r+1)-subset of mu_n, s_lambda(S) is a sum over
SSYT. We use the BIALTERNANT formula s_lambda(x) = det(x_i^{lambda_j + (m-j)}) / Vandermonde,
m=r+1. For 2-row lambda=(a,b) with the rest 0: this is a polynomial.

Plan: measure, for the TRUE maximizer lines, #{S on V} and compare to several candidate
provable upper bounds:
  (B0) C(n,r+1)                      [trivial]
  (B1) (a-b+1)*C(n,r+1)/n  ??        [if V were union of ~(deg-related) cosets]
  (Bcrude) the dilation-orbit count: #{S on V} = n * (#orbits of size n) + (smaller orbits).
We directly measure orbit-size distribution and the count of FULL-size-n orbits.
The real question: is #{S on V} <= K = 2^r C(n/2,r) ALWAYS, or does it break (data says it breaks).
We re-verify the break and then pivot: bound #bad (distinct gamma) not #{S on V}.
"""
from math import comb, gcd
from itertools import combinations
from collections import Counter
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
def analyze(n,e,f,r,P=p):
    a0=r+1; dom=mu_n(n,P); M=max(e-r,e-r+1,f-r,f-r+1,0)
    badS=set(); zero_he=set(); zero_hf=set(); gen=set()
    gammas=set()
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M,P)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1,hfr,hfr1=H(e-r),H(e-r+1),H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%P!=0: continue
        # on V (det=0). Classify:
        if hfr==0:
            zero_hf.add(S); badS.add(S); continue   # gamma = inf (undefined) -- degenerate
        gam=(-her*pow(hfr,P-2,P))%P
        badS.add(S); gammas.add(gam)
        if her==0: zero_he.add(S)   # gamma=0
        else: gen.add(S)
    # orbit structure of badS under shift
    def shift(S): return tuple(sorted((i+1)%n for i in S))
    seen=set(); orbsizes=[]
    for S in badS:
        if S in seen: continue
        orb=set(); cur=S
        while cur not in orb: orb.add(cur); cur=shift(cur)
        seen|=orb; orbsizes.append(len(orb))
    dist=dict(sorted(Counter(orbsizes).items()))
    d=gcd((e-f)%n,n)
    K=(1<<r)*comb(n//2,r)
    print(f"n={n} r={r} line(x^{e},x^{f}) d=gcd(e-f,n)={d}: |lambda|={(e-r)+(f-r+1)}")
    print(f"  #S_on_V={len(badS)}  (he=0 g=0: {len(zero_he)}, hf=0 inf: {len(zero_hf)}, generic: {len(gen)})")
    print(f"  #distinct-gamma(incl 0)={len(gammas)}  #bad-nonzero-gamma~={len(gammas)-(1 if len(zero_he) else 0)}")
    print(f"  orbit-size dist {dist}  #orbits={len(orbsizes)}")
    print(f"  K={K}  S_on_V/K={len(badS)/K:.4f}  C(n,r+1)={comb(n,a0)}  S_on_V/C={len(badS)/comb(n,a0):.4f}")
    return len(badS),K
print("=== r=4 true maximizer (x^{n/2+2},x^{n/4+1}) ===")
for n in [16,32,64]:
    analyze(n, n//2+2, n//4+1, 4)
print("=== r=6 break line (x^20,x^16) at n=32 ===")
analyze(32,20,16,6)
