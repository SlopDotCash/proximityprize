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
    badS=set(); zhe=0; zhf=0; gen=0; gammas=set()
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M,P)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1,hfr,hfr1=H(e-r),H(e-r+1),H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%P!=0: continue
        if hfr==0: zhf+=1; badS.add(S); continue
        gam=(-her*pow(hfr,P-2,P))%P; badS.add(S); gammas.add(gam)
        if her==0: zhe+=1
        else: gen+=1
    def shift(S): return tuple(sorted((i+1)%n for i in S))
    seen=set(); orbsizes=[]
    for S in badS:
        if S in seen: continue
        orb=set(); cur=S
        while cur not in orb: orb.add(cur); cur=shift(cur)
        seen|=orb; orbsizes.append(len(orb))
    dist=dict(sorted(Counter(orbsizes).items()))
    d=gcd((e-f)%n,n); K=(1<<r)*comb(n//2,r)
    print(f"n={n} r={r} (x^{e},x^{f}) d={d} |lam|={(e-r)+(f-r+1)}: #SonV={len(badS)} (g0:{zhe} inf:{zhf} gen:{gen}) #gamma={len(gammas)} orbits{dist} K={K} SonV/K={len(badS)/K:.3f} SonV/C={len(badS)/comb(n,a0):.3f}")
print("r=4 maximizer:")
for n in [16,32]: analyze(n,n//2+2,n//4+1,4)
print("r=6 break line n=32 (x^20,x^16):"); analyze(32,20,16,6)
print("r=6 #bad-max n=32 (x^20,x^18):"); analyze(32,20,18,6)
print("r=3 calib:"); analyze(16,8,7,3); analyze(32,16,15,3)
