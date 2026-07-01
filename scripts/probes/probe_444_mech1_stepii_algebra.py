"""
probe_444_mech1_stepii_algebra.py -- PIN DOWN step (i)+(ii) algebra exactly, separating
PROVEN from CONJECTURED.

(i)  same parity => W_gamma(-x)=(-1)^e W_gamma(x).   [PROVEN trivially]
(ii) Two distinct 'descent' statements; verify which hold and on what hypothesis:

  (ii-a) [the equivariance, PROVEN] For ANY S (not nec. symmetric), gamma(ιS)=(-1)^{e-f}gamma(S)
         because P_i(ιS)=(-1)^i P_i(S) => h_m(ιS) = ??? -- actually h_m(ιS) is NOT (-1)^m h_m(S)
         in general.  The clean statement is gamma(g·S)=g^{e-f}gamma(S) for g in mu_n (dilation),
         applied at g=ι.  VERIFY directly: h_m(g·S)=g^m h_m(S) (homogeneity of h_m).  This IS an
         identity (h_m is homogeneous of degree m).  Hence gamma=-h_{e-r}/h_{f-r} scales by
         g^{(e-r)-(f-r)}=g^{e-f}.  PROVEN.  At g=ι=-1: factor (-1)^{e-f}.

  (ii-b) [the antipodal-symmetric descent convolution, hypothesis-LADEN]
         If S = SQ-pairs ∪ T-singletons where SQ are antipodal pairs {x,-x} and T are antipode-free,
         then h_m(S)=sum_s h_s({x^2 : pairs}) h_{m-2s}(T) and for FULLY symmetric S (T=∅):
         h_{2j}(S)=h_j(S_half^2), h_odd(S)=0.   This is TRUE but only applies to antipodally
         SYMMETRIC S, which (we showed) bad subsets are NOT.

This probe verifies:
  (V1) h_m(g·S)=g^m h_m(S) exactly (the real engine of the equivariance) -- PROVEN identity.
  (V2) the convolution h_m(S)=sum_s h_s(SQ_sq) h_{m-2s}(T) for S=pairs∪singletons.
  (V3) explicitly that for the same-parity maximizer, bad S are NOT antipodally symmetric, so
       (ii-b) descent is INAPPLICABLE -- the honest blocker.
"""
import sys
from math import comb, gcd
from itertools import combinations
import random

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

def test_V1(n,p):
    w=gen(n,p); random.seed(1); ok=tot=0
    for _ in range(200):
        a0=random.randint(3,6)
        S=random.sample(range(n),a0); g=pow(w,random.randrange(n),p)
        elts=[pow(w,i,p) for i in S]; gelts=[(g*z)%p for z in elts]
        M=8; H=hpow(elts,M,p); Hg=hpow(gelts,M,p)
        for m in range(M+1):
            tot+=1
            if Hg[m]==(pow(g,m,p)*H[m])%p: ok+=1
    return ok,tot

def test_V2(n,p):
    w=gen(n,p); half=n//2; random.seed(2); ok=tot=0
    for _ in range(120):
        npairs=random.randint(1,3); nsing=random.randint(0,3)
        pidx=random.sample(range(half),npairs)
        rest=[i for i in range(half) if i not in pidx]+[i for i in range(half,n) if (i-half) not in pidx]
        sing=random.sample(rest,min(nsing,len(rest)))
        S=[]; SQsq=[]
        for i in pidx:
            x=pow(w,i,p); S+= [x,(p-x)%p]; SQsq.append((x*x)%p)
        T=[pow(w,i,p) for i in sing]; S+=T
        if len(set(S))!=len(S): continue
        M=8; H=hpow(S,M,p); Hsq=hpow(SQsq,M,p); HT=hpow(T,M,p)
        for m in range(M+1):
            tot+=1
            conv=0
            for s in range(0,m//2+1):
                conv=(conv+Hsq[s]*HT[m-2*s])%p
            if conv==H[m]: ok+=1
    return ok,tot

def test_V3(n,r,p):
    """same-parity maximizer: are ANY bad subsets antipodally symmetric? what fraction?"""
    w=gen(n,p); a0=r+1; half=n//2
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n,p) for S in subs]
    best=(0,None)
    for e in range(r,n):
        for f in range(r,n):
            if e==f or (e-f)%2: continue
            if max(e-r+1,f-r+1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d; cos=set()
            for H in Hc:
                if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
                if H[f-r]==0: continue
                g=(-H[e-r]*pow(H[f-r],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            if len(cos)>best[0]: best=(len(cos),(e,f))
    e,f=best[1]
    nbad=0; nsym=0
    for Sidx in subs:
        xs=[pow(w,i,p) for i in Sidx]; H=hpow(xs,max(e-r+1,f-r+1),p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        nbad+=1
        Si=set(Sidx)
        if all(((i+half)%n) in Si for i in Sidx): nsym+=1
    return (e,f),nbad,nsym

if __name__=="__main__":
    for p in PRIMES[:1]:
        ok1,t1=test_V1(16,p); ok2,t2=test_V2(16,p)
        print(f"(V1) h_m(g.S)=g^m h_m(S) homogeneity [PROVEN identity]: {ok1}/{t1}")
        print(f"(V2) convolution h_m(S)=sum_s h_s(SQ^2) h_(m-2s)(T) [pairs+singletons]: {ok2}/{t2}")
        for r in [4,5,6]:
            line,nbad,nsym=test_V3(16,r,p)
            print(f"(V3) r={r} same-par max {line}: #bad={nbad}, #antipodally-SYMMETRIC bad={nsym} "
                  f"({100*nsym/nbad:.1f}%) -> (ii-b) applies to only this fraction")
