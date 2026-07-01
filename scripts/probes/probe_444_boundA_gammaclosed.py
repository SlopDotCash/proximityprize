"""
probe_444_boundA_gammaclosed.py -- find the CLOSED FORM of gamma^n at r=3 to make the count
airtight for ALL n.

Strategy: gamma is a degree-1 dilation coordinate (gamma(gS)=g gamma(S)). On the bad locus with
P=1 normalization (ab=1, cd=-1), gamma is a specific function. We want gamma as a function of the
free parameters (a, c) [b=1/a, d=-1/c], then gamma^n in closed form.

We TEST whether gamma has a clean form, e.g. gamma = c1*(s1+s2)+... or gamma = product/linear in
the roots, by computing gamma at many bad S in the P=1 slice and regressing against natural
quantities: s1=a+1/a, s2=c-1/c, e1=s1+s2, and the Vandermonde/discriminant.

Actually the cleanest: since J=gamma^n and we SHOWED #J=#((s1+s2)^2)=C(n/4,2), and J<->I3 is a
bijection, we just need: gamma^n is a function of (s1+s2)^2 (equivalently of e1^2/P since e1=s1+s2
when P=1). Test: gamma^n determined by (s1+s2)? by (s1+s2)^2? and the fiber structure.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import defaultdict
PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,4000):
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
def inv(a,p): return pow(a,p-2,p)

def study(n,p):
    r=3; e,f=n//2,n//2-1; w=gen(n,p); nd=n; M=max(e-r+1,f-r+1)
    sq=[pow(w,2*i,p) for i in range(n//2)]; ns=[pow(w,2*i+1,p) for i in range(n//2)]
    # P=1 slice: a in sq, b=1/a; c in ns, d=-1/c, all distinct
    rows=[]
    for a in sq:
        b=inv(a,p)
        if b==a: continue
        for c in ns:
            d=(-inv(c,p))%p
            if d==c: continue
            S=[a,b,c,d]
            if len(set(S))<4: continue
            H=hpow(S,M,p)
            if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
            if H[f-r]==0: continue
            g=(-H[e-r]*pow(H[f-r],p-2,p))%p
            if not g: continue
            J=pow(g,nd,p)
            s1=(a+b)%p; s2=(c+d)%p; e1=(s1+s2)%p
            rows.append((J,g,s1,s2,e1))
    OP=len(set(r0[0] for r0 in rows))
    # is gamma^n=J determined by (s1+s2)? by (s1+s2)^2?
    by_e1=defaultdict(set); by_e1sq=defaultdict(set)
    for J,g,s1,s2,e1 in rows:
        by_e1[e1].add(J); by_e1sq[(e1*e1)%p].add(J)
    det_e1=all(len(v)==1 for v in by_e1.values())
    det_e1sq=all(len(v)==1 for v in by_e1sq.values())
    # inj of e1sq->J
    e1sq2J=defaultdict(set)
    for J,g,s1,s2,e1 in rows: e1sq2J[(e1*e1)%p].add(J)
    inj=len(set(next(iter(v)) for v in e1sq2J.values()))==len(e1sq2J)
    return dict(OP=OP,det_e1=det_e1,det_e1sq=det_e1sq,n_e1sq=len(by_e1sq),inj=inj,C=comb(n//4,2))

if __name__=="__main__":
    p=PRIMES[0]
    print("P=1 slice: is gamma^n determined by e1=(s1+s2)? by e1^2? (e4=-1 fixed here)")
    for n in [16,32,64,128]:
        R=study(n,p)
        print(f"  n={n}: O_P={R['OP']} det-by-e1={R['det_e1']} det-by-e1^2={R['det_e1sq']} "
              f"#e1^2-values={R['n_e1sq']} e1^2->J inj={R['inj']} C(n/4,2)={R['C']} "
              f"match={R['n_e1sq']==R['C']}")
