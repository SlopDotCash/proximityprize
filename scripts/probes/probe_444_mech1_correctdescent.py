"""
probe_444_mech1_correctdescent.py -- find the CORRECT descent (if any) behind O_P<=C(n/2,r-1).

Established facts (this session, all exact-verified):
 - gamma(gS)=g^{e-f} gamma(S); antipode ι=w^{n/2} gives gamma(ιS)=(-1)^{e-f}gamma(S).
   Same parity => ι FIXES gamma.  (proven 100%)
 - J=gamma^{n/d}, d=gcd(e-f,n).  For same parity, d even => nd=n/d <= n/2.
 - REFUTED: J factors through S^2 multiset (H1), even power sums (H3), odd-hit antipodal
   pairset constant per J (S3).  So naive mu_{n/2} folding of S does NOT determine J.
 - (S2) all J are squares mod p -- but this is TRIVIAL since nd is even (gamma^{even}=square).

This probe tests the remaining plausible descents:
 D1: J depends only on the multiset {s^{nd}} (the nd-th powers, landing in mu_{n/d'} small group).
 D2: gamma is a RATIONAL FUNCTION of e_*(S) but the bad-variety projection gamma:V->P^1 has
     DEGREE related to C(n/2,r-1); measure the fiber sizes |{S bad : J(S)=j0}| -- are they
     CONSTANT (=> O_P=#bad/fibersize, a clean count)?
 D3: the SHARP count: is O_P EXACTLY equal to some clean C(n/2,r-1)-family expression at the
     maximizer?  Tabulate O_P at the same-parity maximizer for n=16,32 and fit.

Also: re-examine whether the maximizer is REALLY same-parity by reporting, per (r,n), the
GLOBAL maximizer line and its parity, and the same-parity maximizer, side by side.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import defaultdict, Counter

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

def collect(n,r,e,f,w,p):
    """return dict gamma->list of Sidx (bad, nonzero gamma)."""
    g2S=defaultdict(list)
    for Sidx in combinations(range(n),r+1):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: g2S[g].append(Sidx)
    return g2S

def find_max(n,r,p,sameparity):
    w=gen(n,p); a0=r+1
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n,p) for S in subs]
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
    return w,best

def run(n,r,p):
    w,(opG,lineG,dG)=find_max(n,r,p,False)
    _,(opS,lineS,dS)=find_max(n,r,p,True)
    print(f"r={r} n={n}: GLOBAL max O_P={opG} at {lineG} parity({lineG[0]%2},{lineG[1]%2}); "
          f"SAME-PARITY max O_P={opS} at {lineS}.  same==global? {opS==opG}")
    # analyze the SAME-PARITY maximizer with D1/D2
    e,f=lineS; d=dS; nd=n//d
    g2S=collect(n,r,e,f,w,p)
    Jto=defaultdict(list)
    for g,Ss in g2S.items():
        Jto[pow(g,nd,p)].extend(Ss)
    OP=len(Jto); bound=comb(n//2,r-1)
    fibers=Counter(len(v) for v in Jto.values())
    # D1: J depends only on {s^{nd}}?
    D1=defaultdict(set)
    for g,Ss in g2S.items():
        J=pow(g,nd,p)
        for S in Ss:
            key=tuple(sorted((nd*i)%n for i in S))
            D1[key].add(J)
    d1ok=all(len(v)==1 for v in D1.values())
    print(f"    [same-parity max (x^{e},x^{f}) d={d} nd={nd}] O_P={OP} bound=C(n/2,{r-1})={bound} ratio={OP/bound:.3f}")
    print(f"    D2 fiber-size dist (|bad S| per J): {dict(sorted(fibers.items()))}  (constant fiber? {len(fibers)==1})")
    print(f"    D1 J factors through {{s^nd}} multiset: {d1ok} (#keys={len(D1)})")

if __name__=="__main__":
    todo=[(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for p in PRIMES[:1]:
        for (r,n) in todo: run(n,r,p)
