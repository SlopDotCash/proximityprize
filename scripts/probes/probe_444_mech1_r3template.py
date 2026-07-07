"""
probe_444_mech1_r3template.py -- understand the PROVEN r=3 structure (4-subset bad <=> 2 squares
{a,b} + 2 nonsquares {c,d} with ab=-cd, giving O_P=C(n/4,2)) and test whether the SAME-PARITY
maximizer at r=4,5,6 admits an analogous "J determined by (r-1)-subset of a coset structure".

r=3 facts to reproduce:
  - maximizer line is OPPOSITE parity (x^{n/2},x^{n/2-1}); O_P=C(n/4,2).
  - bad 4-subsets: exactly 2 in squares mu_{n/2}, 2 in nonsquares, with a*b = -c*d.
  - gamma orbit invariant J <-> the value a*b (=-c*d) which is a SQUARE; choosing {a,b} subset of
    the n/4 squares... C(n/4,2) counts unordered pairs of squares (the (r-1)=2-subset of mu_{n/2}/?).

This probe:
  (1) reproduce r=3 square/nonsquare split + product law, and the J<->{a,b}-pair map -> O_P=C(n/4,2).
  (2) for the SAME-PARITY maximizer at r=4,5,6: compute, per bad S, the split of S into
      squares (mu_{n/2}) vs nonsquares; tabulate (#sq,#nonsq); test if J is determined by the
      PRODUCT of the square-part or some elementary-symmetric-of-squares invariant.
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

def analyze(n,r,p,sameparity,label):
    w,(opmax,line,d)=find_max(n,r,p,sameparity)
    e,f=line; nd=n//d
    g2S=collect(n,r,e,f,w,p)
    # square = even index in mu_n
    sqsplit=Counter()  # (#squares,#nonsquares) of S
    # J-determination tests on the square sub-multiset and product
    J_by_sqset=defaultdict(set)     # J determined by the SET of square-indices?
    J_by_sqprod=defaultdict(set)    # J determined by product of squares?
    J_by_nonsqprod=defaultdict(set)
    for g,Ss in g2S.items():
        J=pow(g,nd,p)
        for S in Ss:
            sq=[i for i in S if i%2==0]; nsq=[i for i in S if i%2==1]
            sqsplit[(len(sq),len(nsq))]+=1
            J_by_sqset[tuple(sorted(sq))].add(J)
            prod_sq=1
            for i in sq: prod_sq=prod_sq*pow(w,i,p)%p
            prod_ns=1
            for i in nsq: prod_ns=prod_ns*pow(w,i,p)%p
            J_by_sqprod[prod_sq].add(J)
            J_by_nonsqprod[prod_ns].add(J)
    print(f"  [{label}] r={r} n={n} line=(x^{e},x^{f}) parity({e%2},{f%2}) d={d} nd={nd}: O_P={opmax} bound C(n/2,{r-1})={comb(n//2,r-1)} C(n/4,{r-1})={comb(n//4,r-1)}")
    print(f"     (#sq,#nonsq) split of bad S: {dict(sorted(sqsplit.items()))}")
    print(f"     J det by square-index SET: {all(len(v)==1 for v in J_by_sqset.values())} (#keys={len(J_by_sqset)})")
    print(f"     J det by PRODUCT of squares: {all(len(v)==1 for v in J_by_sqprod.values())} (#keys={len(J_by_sqprod)})")
    print(f"     J det by PRODUCT of nonsquares: {all(len(v)==1 for v in J_by_nonsqprod.values())} (#keys={len(J_by_nonsqprod)})")

if __name__=="__main__":
    p=PRIMES[0]
    print("=== r=3 PROVEN template (global maximizer, opposite-parity) ===")
    analyze(16,3,p,False,"r3-global")
    analyze(32,3,p,False,"r3-global") if '--n32' in sys.argv else None
    print("=== r=4,5,6 SAME-PARITY maximizer ===")
    for r in [4,5,6]:
        analyze(16,r,p,True,f"r{r}-samepar")
