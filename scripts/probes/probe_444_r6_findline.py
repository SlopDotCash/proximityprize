"""
Find the TRUE r=6 maximizer line at n=16 (target O_P=14, #bad maximal). Search admissible (e,f).
O_P = number of dilation orbits of distinct nonzero gamma. gamma(gS)=g^{e-f} gamma(S), orbit n/d,
d=gcd(e-f,n). We compute #bad (distinct nz gamma) and O_P for each candidate line.
Admissibility for the Schur form: need e-r>=0, f-r>=0 (so all four h-indices >=0). r=6 => e,f>=6.
We scan e,f in [6, n-1], f != e. Report top lines by #bad.
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

def complete_homog(S,mmax,pr):
    P=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1):
            zi=(zi*z)%pr; P[j]=(P[j]+zi)%pr
    h=[0]*(mmax+1); h[0]=1
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+P[i]*h[m-i])%pr
        h[m]=(s*pow(m,pr-2,pr))%pr
    return h

def scan(n,r,pr=p):
    w=w_of_order(n,pr); mu=[pow(w,i,pr) for i in range(n)]
    a0=r+1
    # precompute h up to n-1+? we need h indexed up to max(e)-r+1 <= n-1-r+1 = n-r. compute mmax=n
    combs=list(itertools.combinations(range(n),a0))
    Hcache={}
    mmax=n  # safe upper bound for indices
    for Sidx in combs:
        S=[mu[i] for i in Sidx]
        Hcache[Sidx]=complete_homog(S,mmax,pr)
    results=[]
    for e in range(r,n):
        for f in range(r,n):
            if f==e: continue
            i1,i2,i3,i4 = e-r,e-r+1,f-r,f-r+1
            if max(i1,i2,i3,i4)>mmax: continue
            d=gcd((e-f)%n,n); mult=pow(w,(e-f)%n,pr)
            badnz=set()
            for Sidx in combs:
                h=Hcache[Sidx]
                he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
                if (he_r*hf_r1-hf_r*he_r1)%pr!=0: continue
                if hf_r%pr!=0: gam=(-he_r*pow(hf_r,pr-2,pr))%pr
                elif hf_r1%pr!=0: gam=(-he_r1*pow(hf_r1,pr-2,pr))%pr
                else: continue
                if gam!=0: badnz.add(gam)
            # orbit count
            rem=set(badnz); orbs=0
            while rem:
                x0=next(iter(rem)); cur=x0; o=set()
                for _ in range(n): o.add(cur); cur=cur*mult%pr
                orbs+=1; rem-=o
            results.append((len(badnz),orbs,e,f,d))
    results.sort(reverse=True)
    return results

if __name__=="__main__":
    n=16; r=6
    res=scan(n,r)
    print(f"n={n} r={r} TOP lines by #bad (nz distinct gamma):")
    for badnz,orbs,e,f,d in res[:15]:
        print(f"  line(x^{e},x^{f}) d={d}: #bad={badnz} O_P={orbs}  (n/d={n//d})")
