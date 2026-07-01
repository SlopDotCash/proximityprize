"""
probe_444_mech1_antipodepairing.py -- the ONE clean structural consequence of same-parity:
the antipode iota acts on the BAD SET, preserving J, and (for the same-parity maximizer) FREELY.

Claims to verify rigorously (exact):
 (P1) iota = w^{n/2} maps bad subsets to bad subsets (V is dilation-invariant).  [should be 100%]
 (P2) J(iota S) = J(S) for same parity.  [should be 100%, since gamma(iotaS)=gamma(S)]
 (P3) For the same-parity maximizer, iota has NO fixed bad subset (free action) -- so bad subsets
      come in iota-pairs {S, iotaS}, both with the same J.  (=> #bad is EVEN; weak gain.)
 (P4) Does a LARGER subgroup than <iota> fix J?  The full gamma-stabilizer is mu_d
      (d=gcd(e-f,n)); the dilation orbit of S has size n/d, all with DIFFERENT J in general?
      No -- J is the orbit invariant, constant on the n/d-orbit.  So #bad-with-given-J is a
      union of n/d-dilation-orbits.  Measure #orbits per J (the fiber multiplicity).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

p=2013265921
def gen(n):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
def hpow(elts,M):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H
def gam(Sidx,w,e,f,r):
    xs=[pow(w,i,p) for i in Sidx]; H=hpow(xs,max(e-r+1,f-r+1))
    if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: return None
    if H[f-r]==0: return None
    g=(-H[e-r]*pow(H[f-r],p-2,p))%p
    return g if g else None

def maxline(n,r,w,sameparity=True):
    a0=r+1; subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n) for S in subs]
    best=(0,None,0)
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            if sameparity and (e-f)%2: continue
            if max(e-r+1,f-r+1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d; cos=set()
            for H in Hc:
                if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
                if H[f-r]==0: continue
                g=(-H[e-r]*pow(H[f-r],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            if len(cos)>best[0]: best=(len(cos),(e,f),d)
    return best

def run(n,r):
    w=gen(n); op,(e,f),d=maxline(n,r,w); nd=n//d; half=n//2
    P1=P1t=P2=P2t=0; fixed=0; J2orbcount=defaultdict(set)
    badset=set()
    for Sidx in combinations(range(n),r+1):
        g=gam(Sidx,w,e,f,r)
        if g is None: continue
        badset.add(Sidx)
        Santi=tuple(sorted((i+half)%n for i in Sidx))
        ga=gam(Santi,w,e,f,r)
        P1t+=1
        if ga is not None: P1+=1
        if ga is not None:
            P2t+=1
            if pow(g,nd,p)==pow(ga,nd,p): P2+=1
        if Santi==Sidx: fixed+=1  # can't happen (antipode moves every set of odd... ) but check
        # also: is iotaS == S as a set? only if S antipodally symmetric -> already 0%
        J2orbcount[pow(g,nd,p)].add(Sidx)
    # free action: count bad S fixed by iota (as a SET) = antipodally symmetric
    symfixed=sum(1 for S in badset if all(((i+half)%n) in set(S) for i in S))
    print(f"r={r} n={n} same-par max (x^{e},x^{f}) d={d} nd={nd}: O_P={op} #bad={len(badset)}")
    print(f"   (P1) iota maps bad->bad: {P1}/{P1t}")
    print(f"   (P2) J(iota S)=J(S): {P2}/{P2t}")
    print(f"   (P3) iota-FIXED bad subsets (antipodally symmetric): {symfixed}  => free action? {symfixed==0}")
    fibers=Counter(len(v) for v in J2orbcount.values())
    print(f"   (P4) #bad-subsets per J (fiber sizes): {dict(sorted(fibers.items()))}  (#bad even? {len(badset)%2==0})")

if __name__=="__main__":
    todo=[(4,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo: run(n,r)
