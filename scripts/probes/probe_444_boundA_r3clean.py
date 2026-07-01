"""
probe_444_boundA_r3clean.py -- the CLEAN r=3 count, distinct points enforced, = C(n/4,2) exactly,
AND identify the collision structure (why (s1+s2)^2 collapses (n/4)^2 -> C(n/4,2)).

Normalized P=1: a,b=1/a squares distinct => a in mu_{n/2}, a!=1/a i.e. a^2!=1 i.e. a!=+-1.
 a=+-1 excluded (these are the only square roots of 1; a=1 gives a=b). Also a and 1/a give same {a,b}.
 So s1=a+1/a, a in mu_{n/2}\{+-1}, modulo a~1/a => (n/2-2)/2 = n/4-1 values of s1.
c,d=-1/c nonsquares distinct => c != -1/c i.e. c^2 != -1. c^2=-1 has solutions iff -1 is a square
 in... c nonsquare, c^2 square; -1 is a square (shown). c^2=-1 => c is a 4th root of 1 that's a
 primitive one (w^{n/4},w^{3n/4}); are those nonsquares? index n/4: even iff n/4 even iff mu>=3.
 For n>=8, n/4 even => w^{n/4} is a SQUARE, so c^2=-1 has no NONSQUARE solution => no exclusion
 from c=d for nonsquares! and c ~ d=-1/c give same {c,d}. so s2=c-1/c, c nonsquare, mod c~-1/c
 => (n/2)/2 = n/4 values.
So |S1*|=n/4-1, |S2*|=n/4. W=(s1+s2)^2. Claim #distinct W = C(n/4,2). Test + collision analysis.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,4000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def inv(a,p): return pow(a,p-2,p)

def clean_count(n,p):
    w=gen(n,p)
    sq=[pow(w,2*i,p) for i in range(n//2)]
    ns=[pow(w,2*i+1,p) for i in range(n//2)]
    # s1 = a+1/a, a square, a != +-1, mod a~1/a
    S1=set()
    for a in sq:
        if a==1 or a==p-1: continue
        S1.add((a+inv(a,p))%p)
    # s2 = c-1/c, c nonsquare, c != solutions of c^2=-1 (none if those are squares), mod c~-1/c
    S2=set()
    for c in ns:
        if (c*c)%p==p-1: continue   # c^2=-1 excluded (c=d)
        S2.add((c-inv(c,p))%p)
    Ws=set(((s1+s2)%p)**2%p for s1 in S1 for s2 in S2)
    return len(S1),len(S2),len(Ws)

if __name__=="__main__":
    for p in PRIMES:
        print(f"### p={p}")
        for n in [16,32,64,128,256,512,1024]:
            nS1,nS2,nW=clean_count(n,p)
            print(f"  n={n}: |S1*|={nS1}(n/4-1={n//4-1}) |S2*|={nS2}(n/4={n//4}) #distinct W={nW} C(n/4,2)={comb(n//4,2)} match={nW==comb(n//4,2)}")
