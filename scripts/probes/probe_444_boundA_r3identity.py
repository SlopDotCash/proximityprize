"""
probe_444_boundA_r3identity.py -- VERIFY the two exact identities the r=3 proof rests on, so the
argument is airtight (not just 'numerically O_P=C(n/4,2)'):

  (ID1) At line (e,f)=(n/2, n/2-1), a 4-subset S of mu_n is bad (Schur det=0) IFF
        S = {a,b} U {c,d} with a,b in squares (mu_{n/2}), c,d nonsquares, and a*b = -c*d,
        and gamma != 0.  [the clean condition]
  (ID2) On the bad locus, J := gamma^n = e1^4/e4  (the scale-invariant ratio I3), EXACTLY.
        Equivalently gamma^n = e1^4/e4.

We verify both EXHAUSTIVELY over all 4-subsets at several n and both primes (so it's a verified
identity, char-0). We ALSO verify the count assembly:
  O_P = #distinct (e1^4/e4) = #distinct (s1+s2)^2 (P=1 normalization)
      = |S1*||S2*|/2 = (n/4-1)(n/4)/2 = C(n/4,2).
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
def esym(elts,p):
    E=[1]
    for z in elts:
        newE=E+[0]
        for i in range(len(E),0,-1):
            newE[i]=(newE[i]+E[i-1]*z)%p
        E=newE
    return E
def inv(a,p): return pow(a,p-2,p)
def isq(idx): return idx%2==0   # square = even index

def verify(n,p):
    r=3; e,f=n//2,n//2-1; a0=4; w=gen(n,p); nd=n
    M=max(e-r+1,f-r+1)
    id1_ok=True; id2_ok=True; nbad=0
    Js=set()
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        bad = ((H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p==0) and (H[f-r]!=0)
        if not bad:
            # ID1 reverse: if it satisfies the clean condition it must be bad. check clean->bad.
            sq=[i for i in Sidx if isq(i)]; ns=[i for i in Sidx if not isq(i)]
            if len(sq)==2 and len(ns)==2:
                a,b=[pow(w,i,p) for i in sq]; c,dd=[pow(w,i,p) for i in ns]
                if (a*b+c*dd)%p==0:  # ab=-cd
                    # clean condition holds but not bad? => ID1 fails (unless gamma=0)
                    id1_ok=False
            continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        nbad+=1
        # ID1 forward: bad => 2 squares, 2 nonsquares, ab=-cd
        sq=[i for i in Sidx if isq(i)]; ns=[i for i in Sidx if not isq(i)]
        cond = (len(sq)==2 and len(ns)==2)
        if cond:
            a,b=[pow(w,i,p) for i in sq]; c,dd=[pow(w,i,p) for i in ns]
            cond = ((a*b+c*dd)%p==0)
        if not cond: id1_ok=False
        # ID2: gamma^n == e1^4/e4
        J=pow(g,nd,p); E=esym(xs,p)
        I3=(pow(E[1],4,p)*inv(E[4],p))%p
        if J!=I3: id2_ok=False
        Js.add(J)
    OP=len(Js)
    return id1_ok,id2_ok,nbad,OP,comb(n//4,2)

if __name__=="__main__":
    for p in PRIMES:
        print(f"### p={p}")
        for n in [16,32,64]:
            id1,id2,nbad,OP,C=verify(n,p)
            print(f"  n={n}: ID1(bad<=>2sq+2nsq,ab=-cd)={id1}  ID2(gamma^n=e1^4/e4)={id2}  "
                  f"#bad={nbad} O_P={OP} C(n/4,2)={C} match={OP==C}")
