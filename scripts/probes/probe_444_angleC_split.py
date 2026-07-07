"""
probe_444_angleC_split.py -- test the COSET-SPLIT structure of bad S that would explain the
crude bound O_P <= C(n/2, r-1) and (better) reveal the actual governing combinatorics.

The r=3 proof split S into even/odd indices (=the two cosets of mu_{n/2} in mu_n, i.e. squares vs
nonsquares) with each part a root-set of a quadratic, giving rigidity x_a x_b = -x_c x_d.

We test for general (r,n,line):
  (A) the distribution of (#even-index, #odd-index) over bad S  -- is it concentrated?
  (B) the distribution of e_1-on-evens vs e_1-on-odds  -- rigidity relations?
  (C) does gamma depend ONLY on the even-part power sums (or a bounded set)?  i.e. is gamma a
      function of (e_1^even, e_1^odd) or of a small # of coordinates -> explains C(n/2,r-1).
  (D) the orbit-rep S structure: do orbit reps have a FIXED element (say index 0) and the rest
      chosen from n/2 positions -> count C(n/2, r-1)?  [the (r-1) free choices after pinning
      one element per dilation + one structural constraint]
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
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

def study(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; mult=pow(w,(e-f)%n,p); d=gcd((e-f)%n,n)
    g2S=defaultdict(list)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
        if (her*hfr1-hfr*her1)%p: continue
        if hfr==0: continue
        g=(-her*pow(hfr,p-2,p))%p
        if g: g2S[g].append(Sidx)
    nz=set(g2S)
    # orbit reps (canonical: min gamma in orbit)
    rem=set(nz); reps=[]
    while rem:
        x=next(iter(rem)); o=set(); cur=x
        for _ in range(n): o.add(cur); cur=cur*mult%p
        reps.append(x); rem-=o
    OP=len(reps)
    # (A) parity split distribution over ALL bad S
    paritydist=Counter()
    for g,Ss in g2S.items():
        for S in Ss:
            ev=sum(1 for i in S if i%2==0); paritydist[(ev,len(S)-ev)]+=1
    # (D) per-gamma: does each gamma have a bad S whose dilation-canonical form fixes index 0?
    # Each orbit of S under dilation (S -> S+1 mod n) has size n/gcd; pick rep with 0 in S.
    # Count distinct gamma reps and see if reps biject to (r-1)-subsets of some n/2-size set.
    print(f"  r={r} n={n} (x^{e},x^{f}) d={d}: O_P={OP}  C(n/2,r-1)={comb(n//2,r-1)}  O_P<=C(n/2,r-1)? {OP<=comb(n//2,r-1)}")
    print(f"    parity (even,odd) split dist over bad S: {dict(sorted(paritydist.items()))}")
    # (C) is gamma a function of fewer coords? test: gamma determined by (e_1(S even part), e_1(S odd part))?
    pairs=defaultdict(set)
    for g,Ss in g2S.items():
        for S in Ss:
            ev=[pow(w,i,p) for i in S if i%2==0]; od=[pow(w,i,p) for i in S if i%2==1]
            key=(sum(ev)%p, sum(od)%p)
            pairs[key].add(g)
    multi=sum(1 for k,v in pairs.items() if len(v)>1)
    print(f"    (e1_even,e1_odd) -> #distinct gamma: keys={len(pairs)}, keys mapping to >1 gamma={multi} (0 => gamma is a fn of (e1_even,e1_odd))")

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1)}
    todo=[(3,16),(4,16),(5,16),(3,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    print("coset/parity split structure of bad S:")
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
