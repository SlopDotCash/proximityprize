"""
Find r=6 maximizer at n=32 (target O_P=185). The n=16 maximizer was (x^12,x^10) = e-f=2,
near 3n/4. Scan e-f in {+-2} and a focused band first (full scan over n=32 a0=7 = C(32,7)=3.4M
combos * many lines is too heavy). We restrict to e in [r, n-1], f=e-2 and f=e+2 (the e-f=2 family),
plus e-f=1, to locate O_P=185. Then confirm globally on the winning family.
"""
import itertools
from math import comb, gcd
from collections import Counter
p=2013265921

def w_of_order(n,pr):
    e=(pr-1)//n
    for c in range(2,2000):
        h=pow(c,e,pr)
        if pow(h,n,pr)==1 and pow(h,n//2,pr)!=1: return h
    raise RuntimeError

def complete_homog_upto(S,mmax,pr):
    P=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1):
            zi=(zi*z)%pr; P[j]=(P[j]+zi)%pr
    h=[0]*(mmax+1); h[0]=1
    invs=[0]*(mmax+1)
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+P[i]*h[m-i])%pr
        h[m]=(s*pow(m,pr-2,pr))%pr
    return h

def measure_line(n,r,e,f,mu,combs,pr=p):
    w_mult_exp=(e-f)%n
    d=gcd(w_mult_exp,n)
    i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1
    mmax=max(i1,i2,i3,i4)
    badnz=set()
    for Sidx in combs:
        S=[mu[i] for i in Sidx]
        h=complete_homog_upto(S,mmax,pr)
        he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
        if (he_r*hf_r1-hf_r*he_r1)%pr!=0: continue
        if hf_r%pr!=0: gam=(-he_r*pow(hf_r,pr-2,pr))%pr
        elif hf_r1%pr!=0: gam=(-he_r1*pow(hf_r1,pr-2,pr))%pr
        else: continue
        if gam!=0: badnz.add(gam)
    return badnz,d

if __name__=="__main__":
    n=32; r=6; pr=p
    w=w_of_order(n,pr); mu=[pow(w,i,pr) for i in range(n)]
    a0=r+1
    combs=list(itertools.combinations(range(n),a0))
    print(f"n={n} r={r} #combos={len(combs)} -- scanning e-f=2 family (e=f+2), near 3n/4")
    cand=[]
    for e in range(r,n):
        for f in [e-2,e-1]:
            if f<r or f==e: continue
            badnz,d=measure_line(n,r,e,f,mu,combs,pr)
            mult=pow(w,(e-f)%n,pr)
            rem=set(badnz); orbs=0
            while rem:
                x0=next(iter(rem)); cur=x0; o=set()
                for _ in range(n): o.add(cur); cur=cur*mult%pr
                orbs+=1; rem-=o
            cand.append((len(badnz),orbs,e,f,d))
            print(f"  line(x^{e},x^{f}) d={d}: #bad={len(badnz)} O_P={orbs}")
    cand.sort(reverse=True)
    print("TOP:", cand[:5])
