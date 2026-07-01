"""
probe_444_boundA_r3exact.py -- pin the EXACT r=3 invariant formula and its generalization seed.

r=3 maximizer line: (e,f) = (n/2, n/2-1).  ebar=n/2, fbar=n/2-1. r+1=4-subset S.
PROVEN clean condition: S bad <=> S = {a,b} (squares) U {c,d} (nonsquares) with a*b = -c*d.
And J = gamma^{n/d}.  We compute J as a function of (a,b,c,d) explicitly and identify the map.

Hypothesis to confirm and then generalize:
  At this line, gamma = -h_{ebar-3}(S)/h_{fbar-3}(S) = -h_{n/2-3}(S)/h_{n/2-4}(S).
  We want J = gamma^{n/d}.  We test:
   (R1) J depends ONLY on the unordered pair of products {a*b, c*d} (= {P, -P}); i.e. on P=a*b up
        to the sign-linked partner. Since a,b squares, P=ab is a square; c,d nonsquares, cd is a
        square too, and cd=-ab. So P=ab determines everything? test J=f(P).
   (R2) #distinct P over valid (a,b squares with ab=P) gives the count. a,b in mu_{n/2} (squares),
        unordered distinct => P=ab ranges over... products of 2 distinct squares.
        #distinct ab = ? and matches O_P=C(n/4,2)?  squares = mu_{n/2}? NO: squares in mu_n are
        the index-even elements = <w^2> = mu_{n/2}. Wait mu_{n/2}=<w^2> has n/2 elements = the
        squares. a,b distinct squares: ab = w^{2i+2j}, i<j in 0..n/2-1 => ab in mu_{n/2}, and
        #distinct {i+j mod n/2 : i<j} ... but C(n/4,2) suggests a FURTHER halving to mu_{n/4}.
  We measure: the map S=(a,b,c,d) -> J, and tabulate J vs (P=ab, parities), to get the exact
  generating set and confirm |image|=C(n/4,2).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
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

def r3study(n,p):
    r=3; e,f=n//2,n//2-1; a0=4
    w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d   # e-f=1 => d=1, nd=n
    M=max(e-r+1,f-r+1)
    # collect bad S with structure
    J2data=defaultdict(list)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        # classify squares (even index) vs nonsquares
        sq=[i for i in Sidx if i%2==0]; nsq=[i for i in Sidx if i%2==1]
        # P = product of the squares (as field elt) and of nonsquares
        Psq=1
        for i in sq: Psq=Psq*pow(w,i,p)%p
        Pnsq=1
        for i in nsq: Pnsq=Pnsq*pow(w,i,p)%p
        J2data[J].append((len(sq),len(nsq),Psq,Pnsq, tuple(sorted(sq)), tuple(sorted(nsq))))
    OP=len(J2data)
    # Does (#sq,#nsq) = (2,2) for all bad S?
    types=Counter()
    for J,L in J2data.items():
        for t in L: types[(t[0],t[1])]+=1
    # Is J determined by Psq (= a*b)? collect map Psq -> set of J
    Psq2J=defaultdict(set); J2Psq=defaultdict(set)
    for J,L in J2data.items():
        for t in L:
            Psq2J[t[2]].add(J); J2Psq[J].add(t[2])
    J_det_by_Psq = all(len(v)==1 for v in Psq2J.values())
    Psq_const_per_J = all(len(v)==1 for v in J2Psq.values())
    ndistinctPsq=len(Psq2J)
    # what is Psq=a*b? index = sum of two distinct even indices = even. range over mu_{n/2}.
    # the count of distinct Psq among bad:
    return dict(OP=OP,types=dict(types),J_det_by_Psq=J_det_by_Psq,
                Psq_const_per_J=Psq_const_per_J,ndistinctPsq=ndistinctPsq,
                Cn4_2=comb(n//4,2),Cn2_2=comb(n//2,2))

if __name__=="__main__":
    for p in PRIMES:
        print(f"### p={p}")
        for n in [16,32,64]:
            R=r3study(n,p)
            print(f"  n={n}: O_P={R['OP']} C(n/4,2)={R['Cn4_2']} C(n/2,2)={R['Cn2_2']}")
            print(f"     types(#sq,#nsq)={R['types']}")
            print(f"     J determined by P=ab? {R['J_det_by_Psq']}  P=ab const per J? {R['Psq_const_per_J']}  #distinct P={R['ndistinctPsq']}")
            if n>=64: break
