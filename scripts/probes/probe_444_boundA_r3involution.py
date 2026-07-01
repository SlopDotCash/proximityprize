"""
probe_444_boundA_r3involution.py -- identify the 2-to-1 collision making #(s1+s2)^2 = |S1*||S2*|/2.

The product map phi:(s1,s2) -> (s1+s2)^2 on S1* x S2* (sizes n/4-1, n/4) has image C(n/4,2)
= |S1*||S2*|/2. So phi is EXACTLY 2-to-1 onto its image (no other collisions, no fixed/branch pts).
We find the involution iota on S1* x S2* with phi(iota(x))=phi(x), iota fixed-point-free.

Candidate: (s1+s2)^2=(s1'+s2')^2 <=> s1+s2 = -(s1'+s2'). Note S1* is the set of a+1/a (a square):
this set is SYMMETRIC under negation? -(a+1/a)=(-a)+(-1/a)=(-a)+1/(-a) => -s1 = (-a)+1/(-a). -a:
a square, -1 square => -a square. So -s1 in S1* too! S1* is closed under negation (s1 -> -s1).
Similarly s2=c-1/c, -s2 = (-c)-1/(-c)?? -(c-1/c) = -c+1/c = (-c)-1/(-c)?? (-c)-1/(-c)=-c+1/c = -s2. yes.
-c: c nonsquare, -1 square => -c nonsquare. So S2* closed under negation too.
So iota(s1,s2)=(-s1,-s2) gives phi=(-s1-s2)^2=(s1+s2)^2. Fixed pts: s1=-s1 => 2s1=0 => s1=0;
is 0 in S1*? s1=a+1/a=0 => a^2=-1 => a square root of -1 = w^{n/4} (square, index n/4 even) => yes
a=w^{n/4} is a SQUARE with a+1/a=0!? but we EXCLUDED a=+-1 only, not a^2=-1. Hmm so s1=0 might be
in S1*. Check: that would be a fixed point of iota on the s1 coordinate; pair (0,s2)->(s2)^2 and
(-0,-s2)=(0,-s2)->(s2)^2 same, but as elements (0,s2)!=(0,-s2) unless s2=0. so still 2-to-1 via s2.
We just VERIFY computationally: iota=(-s1,-s2) is fixed-point-free on S1*xS2* and phi-collisions are
EXACTLY the iota-orbits (=> image=|prod|/2). Also check the alt involution (s1,s2)->(-s1,-s2) only.
"""
import sys
from math import comb
from collections import defaultdict
PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,4000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def inv(a,p): return pow(a,p-2,p)
def sets(n,p):
    w=gen(n,p)
    sq=[pow(w,2*i,p) for i in range(n//2)]; ns=[pow(w,2*i+1,p) for i in range(n//2)]
    S1=set();
    for a in sq:
        if a==1 or a==p-1: continue
        S1.add((a+inv(a,p))%p)
    S2=set()
    for c in ns:
        if (c*c)%p==p-1: continue
        S2.add((c-inv(c,p))%p)
    return S1,S2
if __name__=="__main__":
    p=PRIMES[0]
    for n in [16,32,64,128,256]:
        S1,S2=sets(n,p)
        S1=sorted(S1); S2=sorted(S2)
        # closure under negation:
        negS1 = all(((-s)%p) in set(S1) for s in S1)
        negS2 = all(((-s)%p) in set(S2) for s in S2)
        # phi fibers
        phi=defaultdict(list)
        for s1 in S1:
            for s2 in S2:
                phi[((s1+s2)%p)**2%p].append((s1,s2))
        fibersz=set(len(v) for v in phi.values())
        # are all fibers exactly the iota=(-s1,-s2) orbit (size 2, since fixed-point-free)?
        iota_ok=True; ffree=True
        for v in phi.values():
            if len(v)!=2: iota_ok=False
            for (s1,s2) in v:
                if ((-s1)%p,(-s2)%p) not in set(v): iota_ok=False
                if (-s1)%p==s1 and (-s2)%p==s2: ffree=False
        print(f"n={n}: |S1*|={len(S1)} |S2*|={len(S2)} prod={len(S1)*len(S2)} "
              f"|image|={len(phi)} C(n/4,2)={comb(n//4,2)} fibersizes={fibersz} "
              f"negClosed(S1,S2)=({negS1},{negS2}) iota-2to1={iota_ok} ffree={ffree}")
