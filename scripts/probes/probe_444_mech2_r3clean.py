"""
probe_444_mech2_r3clean.py -- REVERSE-ENGINEER the proven r=3 map to find what Phi actually is,
then test the SAME recipe at r=4,5,6.

PROVEN r=3 clean condition (from CONTEXT): a 4-subset S is bad (on line x^{n/2},x^{n/2-1}) iff
S = {a,b}+{c,d} with a,b in SQUARES mu_{n/2}, c,d NON-squares, and a*b = -c*d.
And O_P=C(n/4,2): the count is over 2-subsets of mu_{n/4} (= squares-of-squares). So the (r-1)=2
'data' that pins J is a 2-subset of mu_{n/4}, NOT mu_{n/2}.  (C(n/4,2) not C(n/2,2).)

So for r=3 the proven count is C(n/4, r-1) = C(n/4,2), STRICTLY SMALLER than the conjecture
C(n/2,r-1)=C(n/2,2).  The conjecture O_P<=C(n/2,r-1) is loose at r=3; the SHARP count uses mu_{n/4}.

GOAL: find the ACTUAL invariant.  For r=3, what 2-subset of mu_{n/4} does J map to?
Candidates for the r=3 map Phi(J):
  - the pair {a*b} ... = -c*d is a single value (product). For O_P=C(n/4,2) we need a 2-subset.
  - the UNORDERED pair {a/b-class, ...}?  Let's just COMPUTE: for each J, look at all bad S,
    decompose each into squares-part {a,b} and nonsquares-part {c,d}, and find the invariant.

We brute-force the structure and PRINT the actual algebraic invariant that is constant across the
n/d-orbit and distinct across J, hunting for the 2-subset-of-mu_{n/4} it corresponds to.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def collect(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list)
    Mmax=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J2S[pow(g,nd,p)].append(Sidx)
    return w,J2S,d,nd

def r3_decompose(n,p=P):
    """For r=3 line (n/2,n/2-1): verify the clean condition, and find the invariant 2-subset of
       mu_{n/4} for each J."""
    r,e,f=3,n//2,n//2-1
    w,J2S,d,nd=collect(n,r,e,f,p)
    half=n//2
    print(f"  r=3 n={n}: O_P={len(J2S)} C(n/4,2)={comb(n//4,2)}")
    # squares of mu_n are even-index; mu_{n/4} are indices divisible by 4.
    for J,Ss in sorted(J2S.items())[:8]:
        feats=[]
        for S in Ss:
            evens=[i for i in S if i%2==0]; odds=[i for i in S if i%2==1]
            # in mu_n, w^i is a square iff i even. so squares-part=evens, nonsquares=odds.
            # product a*b: sum of even indices mod n; c*d: sum of odd indices.
            # the proven invariant 2-subset of mu_{n/4}: ?
            feats.append((len(evens),len(odds),
                          sum(evens)%n, sum(odds)%n))
        print(f"    J={J}: #S={len(Ss)} (sq,nonsq,prodSqIdx,prodNonsqIdx) set="
              f"{sorted(set(feats))[:6]}")

if __name__=="__main__":
    for n in [16,32]:
        r3_decompose(n)
