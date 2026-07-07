"""FINAL Angle-A verdict probe. Confirm, over TWO primes (char-0), that even the GENERIC-PINNED
part of V (he!=0, hf!=0 -> a genuine finite nonzero gamma, NOT the degenerate strata) overshoots
K = 2^r C(n/2,r) at the r=6 break line (x^20,x^16), n=32. This kills Angle A even after quotienting
the degenerate (gamma=0 / gamma=inf) loci. Calibrate r=3 first."""
from math import comb
from itertools import combinations
def mu_n(n,P):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return [pow(h,i,P) for i in range(n)]
def h_upto(Sv,M,P):
    h=[0]*(M+1); h[0]=1
    for z in Sv:
        new=[0]*(M+1); prev=0
        for m in range(M+1): prev=(h[m]+z*prev)%P; new[m]=prev
        h=new
    return h
def classify(n,e,f,r,P):
    a0=r+1; dom=mu_n(n,P); M=max(e-r,e-r+1,f-r,f-r+1,0)
    tot=0; gen=0
    for S in combinations(range(n),a0):
        Sv=[dom[i] for i in S]; hv=h_upto(Sv,M,P)
        H=lambda m: hv[m] if 0<=m<=M else 0
        her,her1,hfr,hfr1=H(e-r),H(e-r+1),H(f-r),H(f-r+1)
        if (her*hfr1-hfr*her1)%P!=0: continue
        tot+=1
        if her!=0 and hfr!=0: gen+=1
    return tot,gen
for P in [2013265921, 3221225473]:
    print(f"--- prime {P} ---")
    # calibrate r=3 n=16,32
    for (n,e,f,r) in [(16,8,7,3),(32,16,15,3)]:
        t,g=classify(n,e,f,r,P); print(f"  CALIB r=3 n={n}: #SonV={t} generic={g} (O_P calib via gamma elsewhere)")
    # break line
    n,e,f,r=32,20,16,6; K=(1<<r)*comb(n//2,r)
    t,g=classify(n,e,f,r,P)
    print(f"  BREAK r=6 n=32 (x^20,x^16): #SonV={t} generic-pinned={g} K={K}")
    print(f"    #SonV/K={t/K:.4f}  generic/K={g/K:.4f}  -> generic alone > K? {g>K}")
