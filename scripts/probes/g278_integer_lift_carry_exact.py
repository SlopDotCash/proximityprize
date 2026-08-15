#!/usr/bin/env python3
"""G278 exact integer-lift carry census for the #466 adjacent-rank CORE alignment.

For the order-n dyadic subgroup G <= F_p^*, represented by integers 1..p-1, count
  J_{r,k} = #{(y,z,A,B): y,z in G, |A|=r, |B|=r-1,
                            2*y + sum(B) - z - sum(A) = k*p}.
Then J_r=sum_k J_{r,k} and A_r=p*J_r-n^2*C(n,r)*C(n,r-1).

Every count below is exact. Subset integer-sum profiles use uint64 dynamic programming.
Only needed difference coefficients are computed by exact uint64 dot products, never FFT.
All totals are independently cross-checked against a modular subset-sum computation.
The largest possible total in the cells below is < 2^64, asserted before every dot product.
"""
from __future__ import annotations
from math import comb, floor, ceil
from collections import defaultdict
import numpy as np


def prime_factors(x:int):
    out=[]; d=2
    while d*d<=x:
        if x%d==0:
            out.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: out.append(x)
    return out


def primitive_root(p:int):
    fs=prime_factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError("no primitive root")


def subgroup(p:int,n:int):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    G=[]; x=1
    for _ in range(n): G.append(x); x=x*h%p
    assert x==1 and len(set(G))==n and all(0<x<p for x in G)
    return sorted(G)


def subset_integer_sum(G:list[int],r:int):
    cap=r*max(G)
    dp=[np.zeros(cap+1,dtype=np.uint64) for _ in range(r+1)]
    dp[0][0]=1
    for used,x in enumerate(G,1):
        for k in range(min(r,used),0,-1):
            src=dp[k-1]; take=min(len(src),len(dp[k])-x)
            if take: dp[k][x:x+take]+=src[:take]
    assert int(dp[r].sum())==comb(len(G),r)
    return dp[r]


def exact_diff_at(A:np.ndarray,B:np.ndarray,d:int,total_bound:int):
    """sum_s A[s]*B[s-d], exact in uint64 because result <= total_bound < 2^64."""
    assert total_bound < 2**64
    lo=max(0,d); hi=min(len(A),len(B)+d)
    if lo>=hi: return 0
    v=np.dot(A[lo:hi],B[lo-d:hi-d])
    return int(v)


def modular_alignment(p:int,G:list[int],r:int):
    H=[np.zeros(p,dtype=np.uint64) for _ in range(r+1)]; H[0][0]=1
    for used,x in enumerate(G,1):
        for k in range(min(r,used),0,-1): H[k]+=np.roll(H[k-1],x)
    W=defaultdict(int)
    for y in G:
        for z in G: W[(2*y-z)%p]+=1
    total_bound=comb(len(G),r)*comb(len(G),r-1)
    J=0
    for x,w in W.items():
        # R(x)=sum_s H_r(s)*H_{r-1}(s-x)
        val=int(np.dot(H[r],np.roll(H[r-1],x)))
        assert val<=total_bound
        J+=w*val
    return J


def lawful_antipodal(n:int,r:int):
    m=n//2
    if r==5:
        return n*(m-2)*(m-1)*(203*m*m-1099*m+1536)//12
    if r==6:
        return n*(m-2)*(m-1)*(287*m**3-2789*m*m+9174*m-10160)//20
    raise ValueError(r)


def carry_census(p:int,n:int,r:int):
    G=subgroup(p,n)
    Aprof=subset_integer_sum(G,r); Bprof=subset_integer_sum(G,r-1)
    total_pairs=comb(n,r)*comb(n,r-1)
    assert total_pairs<2**64
    W=defaultdict(int)
    for y in G:
        for z in G: W[2*y-z]+=1
    cache={}; carr=defaultdict(int)
    dmin=-(r-1)*max(G); dmax=r*max(G)
    for d1,w in W.items():
        klo=floor((d1-dmax)/p)-1; khi=ceil((d1-dmin)/p)+1
        for k in range(klo,khi+1):
            d=d1-k*p
            if d<dmin or d>dmax: continue
            if d not in cache: cache[d]=exact_diff_at(Aprof,Bprof,d,total_pairs)
            carr[k]+=w*cache[d]
    carr={k:v for k,v in carr.items() if v}
    J=sum(carr.values()); Jmod=modular_alignment(p,G,r)
    assert J==Jmod,(p,n,r,J,Jmod)
    # Negation bijection: exact observed shell symmetry.
    assert all(carr.get(k,0)==carr.get(-k,0) for k in carr)
    B=n*n*comb(n,r)*comb(n,r-1); gate=p*J-B; need=B//p+1
    law=lawful_antipodal(n,r)
    J0=carr.get(0,0); Enz=J-J0; residual_need=need-law
    assert 0<=law<=J0<=J
    return dict(p=p,n=n,r=r,G=G,carr=carr,J=J,B=B,gate=gate,need=need,law=law,
                J0=J0,Enz=Enz,E0=J0-law,residual_need=residual_need,
                zero_insufficient=J0<need,nonzero_insufficient=Enz<residual_need)


def main():
    cells=[
      (433,16,5),(433,16,6),       # both positive, but both carry blocks insufficient
      (577,16,5),(577,16,6),       # adjacent both-negative control
      (3617,32,5),(3617,32,6),     # later both-negative control
      (70753,32,5),(70753,32,6),   # exact G268 split-sign late cell
    ]
    rows=[]
    for c in cells:
        x=carry_census(*c); rows.append(x)
        cs=", ".join(f"{k}:{v}" for k,v in sorted(x['carr'].items()))
        print(f"(n,p,r)=({x['n']},{x['p']},{x['r']}): A={x['gate']:+d}; J={x['J']}; need={x['need']}")
        print(f"  carry {{{cs}}}")
        print(f"  law={x['law']}; J0={x['J0']}; E0={x['E0']}; Eneq0={x['Enz']}; "
              f"residual_need={x['residual_need']}; Eneq0/need={x['Enz']/x['residual_need']:.9f}")
        print(f"  zero_insufficient={x['zero_insufficient']} nonzero_insufficient={x['nonzero_insufficient']}")
    # Hard frontier facts.
    assert all(x['zero_insufficient'] and x['nonzero_insufficient'] for x in rows)
    pos=[x for x in rows if x['gate']>0]; neg=[x for x in rows if x['gate']<0]
    assert {(x['p'],x['r']) for x in pos}=={(433,5),(433,6),(70753,5)}
    assert {(x['p'],x['r']) for x in neg}=={(577,5),(577,6),(3617,5),(3617,6),(70753,6)}
    # Same p=433 witnesses both live ranks: gate positive only after combining BOTH carry blocks.
    for x in pos:
        assert x['J0']<x['need'] and x['Enz']<x['residual_need'] and x['J']>=x['need']
    print("\nG278 EXACT PASS")
    print("Every lawful antipodal packet lies in carry 0; all nonzero carries are pure characteristic-p.")
    print("Yet on every tested rank-5/6 cell, the full nonzero-carry block is below the exact residual")
    print("deficit and carry 0 alone is below the gate. Positive cells need the hidden carry-0")
    print("characteristic-p residual together with nonzero carries. Integer carry does not localize CORE.")

if __name__=='__main__': main()
