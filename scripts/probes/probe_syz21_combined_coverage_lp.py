#!/usr/bin/env python3
"""SYZ21 combined-coverage audit.

Adversarial question (Part B): SYZ20's LP maximises the certified bad-scalar count
over PURE degenerate-core-family profiles (one core size `s`, repeated `D` times,
sunflower min-union, per-core cost `s-k+1`).  But a bad scalar can instead have a
DISTINCT non-degenerate witness (support size `t`, its own G87 block of `t-k`
gamma-weighted functionals in the `2(n-k)`-dim syndrome-PAIR pool), yielding 1 bad
scalar at cost `t-k+1` in the union (attached to the sunflower core, overlap k-1).

Honest combined model.  Every bad scalar is hosted by SOME core of size `s in
[k+1, t]` (a "block"); a block of size `s` costs `s-(k-1)` in the shared union pool
(budget `n-k`, from `2(|U|-k)+1 <= 2(n-k)`) and hosts `yield(s)` bad scalars, where
`yield(s) = (n-s)//(t-s)` for `s<t` and `n-s` for `s>=t` (an independent-block /
non-degenerate scalar is the `s=t-1` or `s=t` end).  So "independent-block singletons"
are NOT a separate uncaptured category -- they are the large-`s` end of the SAME item
menu.  The combined optimum is therefore the full INTEGER KNAPSACK over the shared
pool, which is >= SYZ20's single-item `mergeOpt`.  We compute it and compare to the
survival budget B=n and to SYZ7 empirics.
"""
from fractions import Fraction
import math

def yield_s(n,s,t):
    if s>=t: return n-s
    if t-s<=0: return 0
    return (n-s)//(t-s)

def cost(s,k):            # sunflower incremental union cost
    return s-(k-1)

def full_knapsack(n,k,t):
    """Unbounded integer knapsack: max sum yield s.t. sum cost <= n-k."""
    B = n-k
    items=[]
    for s in range(k+1, n):
        y=yield_s(n,s,t); c=cost(s,k)
        if y>0 and c>0: items.append((c,y,s))
    dp=[0]*(B+1)
    arg=[None]*(B+1)
    for w in range(1,B+1):
        for (c,y,s) in items:
            if c<=w and dp[w-c]+y>dp[w]:
                dp[w]=dp[w-c]+y; arg[w]=(s,c,y,arg[w-c])
    # reconstruct multiset
    best=max(range(B+1), key=lambda w:dp[w])
    multiset={}
    a=arg[best]
    while a is not None:
        s,c,y,prev=a; multiset[s]=multiset.get(s,0)+1; a=prev
    return dp[best], multiset

def single_item(n,k,t):   # SYZ20 mergeOpt reproduction
    B=n-k; best=0; barg=None
    for s in range(k+1,n):
        y=yield_s(n,s,t); c=cost(s,k)
        if y<=0 or c<=0: continue
        D=B//c
        if D*y>best: best=D*y; barg=(s,y,c,D)
    return best,barg

def independent_only(n,k,t):
    """Bad count if EVERY bad scalar is its own independent G87 block:
       D*(t-k)+1 <= 2(n-k)  =>  D <= (2(n-k)-1)//(t-k), each yields 1 scalar."""
    return (2*(n-k)-1)//(t-k)

def johnson(n,k): return 1-math.sqrt(k/n)

for (n,k) in [(64,32),(32,16)]:
    B=n
    print(f"\n===== n={n} k={k}  B(survival)={B}  pair-pool=2(n-k)={2*(n-k)}  Johnson d~{johnson(n,k):.4f} =====")
    print(f"{'t':>3} {'delta':>7} {'zone':>9} {'single':>7} {'knapsack':>9} {'indep':>6} {'B':>4}  {'verdict':>8}  knap-multiset")
    tmax = n-1
    for t in range(k+7, k+16):
        if t>=n: break
        delta=(n-t)/n
        zone="above1/3" if delta>1/3+1e-9 else ("STRIP" if delta>=johnson(n,k)-1e-9 else "belowJ")
        si,_=single_item(n,k,t)
        kn,ms=full_knapsack(n,k,t)
        ind=independent_only(n,k,t)
        verdict = "CLOSES" if kn<B else ("TIE" if kn==B else "LEAK")
        print(f"{t:>3} {delta:>7.4f} {zone:>9} {si:>7} {kn:>9} {ind:>6} {B:>4}  {verdict:>8}  {dict(sorted(ms.items()))}")
