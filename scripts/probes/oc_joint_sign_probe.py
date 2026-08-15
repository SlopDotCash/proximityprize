#!/usr/bin/env python3
"""Joint-sign / joint-covariance structure of (A_5, A_6) at the BGK wall.

The surviving CORE target (per G56 frontier) is the SIGNED SIMULTANEOUS
r=5 AND r=6 covariance A_r = p*sum_t W(t)R_r(t) - n^2 C(n,r)C(n,r-1).
G56 proved every kernel-support statistic (floor, defect, magnitude) is
ORTHOGONAL to sign(A_r). The only surviving mechanism must use genuinely
joint placement data.

This probe asks the sharp joint question that no support statistic answers:
  Q1: is sign(A_5) == sign(A_6) forced, or does the anti-aligned quadrant
      (A_5>0, A_6<0) or (A_5<0, A_6>0) actually occur?
  Q2: if a discordant case exists, is it controlled by an arithmetic
      invariant of p (v2 = v_2(p-1), r=ord_n(...), residues)?
  Q3: is there a conserved SIGN-COUPLING invariant J(p) with
      sign(A_5*A_6) determined -> that would be a genuine joint no-go OR
      a binding lemma.

If sign(A_5)==sign(A_6) is UNIVERSAL, the simultaneous lower bound reduces
to a single-rank bound (huge simplification, potential prize movement).
If it is violated with a clean arithmetic predictor, that predictor is the
new joint invariant. Either outcome is theorem-level information.
"""
from __future__ import annotations
import math, numpy as np

def factor(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out

def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise ValueError(p)

def subgroup(p,n):
    assert (p-1)%n==0
    z=pow(primitive_root(p),(p-1)//n,p)
    G=[]; x=1
    for _ in range(n): G.append(x); x=x*z%p
    assert x==1 and len(set(G))==n
    return G

def subset_hists(G,p,R):
    dp=np.zeros((R+1,p),dtype=object); dp[0,0]=1
    used=0
    for x in G:
        used+=1
        for k in range(min(R,used),0,-1):
            dp[k]=dp[k]+np.roll(dp[k-1],x)
    return dp

def circ_corr_exact(a,b,p):
    # exact integer circular correlation c[t]=sum_x a[x]b[x-t]; python ints
    a=[int(v) for v in a]; b=[int(v) for v in b]
    c=[0]*p
    nz_a=[(x,a[x]) for x in range(p) if a[x]]
    for t in range(p):
        s=0
        for x,av in nz_a:
            bv=b[(x-t)%p]
            if bv: s+=av*bv
        c[t]=s
    return c

def compute_A(G,p,n,r):
    dp=subset_hists(G,p,r)
    GS=set(G)
    W=[0]*p
    for y in G:
        y2=(2*y)%p
        for z in G: W[(y2-z)%p]+=1
    R=circ_corr_exact(dp[r],dp[r-1],p)
    totalR=math.comb(n,r)*math.comb(n,r-1)
    C12=sum(W[t]*R[t] for t in range(p))
    baseline=n*n*totalR
    A=p*C12-baseline
    # centered second moments for correlation sign context
    centeredW=p*sum(x*x for x in W)-n**4
    centeredR=p*sum(x*x for x in R)-totalR*totalR
    return A, centeredW, centeredR

def primes_with_order(n, lo, hi):
    out=[]
    x=lo| 1
    while x<=hi:
        if x>=5 and all(x%q for q in range(2,int(x**0.5)+1)) and (x-1)%n==0:
            out.append(x)
        x+=2
    return out

def v2(m): return (m & -m).bit_length()-1

def main():
    print(f"{'n':>3} {'p':>7} {'v2':>3} {'A5':>22} {'A6':>26} {'s5':>3} {'s6':>3} {'concord':>7}")
    rows=[]
    for n in (8,16,32):
        ps=primes_with_order(n, 5, 4000 if n<32 else 3000)
        for p in ps:
            G=subgroup(p,n)
            A5,_,_=compute_A(G,p,n,5)
            A6,_,_=compute_A(G,p,n,6)
            s5=0 if A5==0 else (1 if A5>0 else -1)
            s6=0 if A6==0 else (1 if A6>0 else -1)
            concord = (s5==s6)
            rows.append((n,p,v2(p-1),A5,A6,s5,s6,concord))
            print(f"{n:>3} {p:>7} {v2(p-1):>3} {A5:>22} {A6:>26} {s5:>3} {s6:>3} {str(concord):>7}")
    print("\n=== JOINT SIGN SUMMARY ===")
    tot=len(rows)
    conc=sum(1 for r in rows if r[7])
    disc=[r for r in rows if not r[7]]
    print(f"total primes: {tot}   concordant sign(A5)==sign(A6): {conc}   discordant: {len(disc)}")
    if disc:
        print("DISCORDANT CASES (the anti-aligned quadrant DOES occur):")
        for r in disc:
            print(f"  n={r[0]} p={r[1]} v2={r[2]} s5={r[5]} s6={r[6]}  A5={r[3]} A6={r[4]}")
        # arithmetic predictor test
        print("\n  predictor test: does v2(p-1) or p mod small classify discordance?")
        from collections import defaultdict
        by_v2=defaultdict(lambda:[0,0])
        for r in rows:
            by_v2[(r[0],r[2])][0 if r[7] else 1]+=1
        for k in sorted(by_v2):
            c,d=by_v2[k]
            print(f"    n={k[0]} v2={k[1]}: concord={c} discord={d}")
    else:
        print("*** sign(A5)==sign(A6) UNIVERSAL in sampled range ***")
        print("    -> simultaneous r=5&6 lower bound may reduce to single-rank")
    # sign(A5) vs sign(A6) correlation coefficient over sampled primes
    s5v=[r[5] for r in rows]; s6v=[r[6] for r in rows]
    agree=sum(1 for a,b in zip(s5v,s6v) if a==b and a!=0)
    print(f"\n  sign-agreement rate: {agree}/{tot} = {agree/tot:.4f}")

if __name__=='__main__':
    main()
