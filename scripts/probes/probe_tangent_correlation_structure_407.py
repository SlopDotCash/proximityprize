#!/usr/bin/env python3
"""
probe_tangent_correlation_structure_407.py  (#407 — BOLD new attack)

The house B is pinned by the power spectrum of the tangent sequence T_h = sum_{w in mu_n} chi^h(1-w).
Its autocorrelation R_T(k) = sum_h T_h conj(T_{h+k}) reduces EXACTLY to a finite combinatorial set:

   R_T(k) = m * sum_{(w,w') in Sol} chi^{-k}(1-w'),
   Sol = {(w,w') in mu_n^2 : (1-w)/(1-w') in mu_n} = {(s,s') in T^2 : s^n = s'^n},  T={1-w}.

BOLD CONJECTURE TO TEST: for 2-power mu_n, Sol has EXACT structure (a small explicit set / involution),
so R_T -- hence the house spectrum, hence B EXACTLY -- is a closed finite formula with NO open analytic
input. If Sol is generic (size ~ c*n, no involution), the wall stands. Either way is decisive.

Measured here:
 1. N = #Sol and N/n (the off-diagonal multiplicity).
 2. fiber sizes c_v = #{w in mu_n, w!=1 : (1-w)^n = v} -- is s|->s^n on T low-collision?
 3. off-diagonal Sol pairs: is w' a FUNCTION of w (an involution)?  what map?
 4. does R_T(k)/m match a SHORT character-sum closed form?
"""
import numpy as np, math
from collections import defaultdict, Counter

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(a,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True

def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        s,x=set(),1
        for _ in range(n):
            s.add(x); x=x*h%p
        if len(s)==n: return sorted(s), g
    return None,None

def analyze(p, n):
    mu,g = subgroup(p,n)
    if mu is None: return None
    mu_set=set(mu)
    m=(p-1)//n
    # T = {1-w : w in mu_n, w!=1}
    Tset = [( (1-w)%p, w) for w in mu if w!=1]   # (s, w)
    # fibers of s |-> s^n
    fib = defaultdict(list)
    for s,w in Tset:
        fib[pow(s,n,p)].append((s,w))
    c_dist = Counter(len(v) for v in fib.values())
    N = sum(len(v)**2 for v in fib.values())     # #Sol
    # off-diagonal structure: for each fiber, list the w's; is there an involution?
    # collect map w -> set of w' (w'!=w) in same fiber
    offdiag_pairs = []
    for v,lst in fib.items():
        ws=[w for s,w in lst]
        for s,w in lst:
            for s2,w2 in lst:
                if w2!=w:
                    offdiag_pairs.append((w,w2))
    # is w2 = -w mod p (antipodal)?  or w2 = w^{-1}? or w2 = 1/w-ish?
    antip = sum(1 for (w,w2) in offdiag_pairs if w2==(p-w)%p)
    inv   = sum(1 for (w,w2) in offdiag_pairs if w2==pow(w,p-2,p))
    # the "w + w' = 1"? (since 1-w, 1-w' ... ) test w2 == (1-w)?? no. test a few candidate maps:
    one_minus = sum(1 for (w,w2) in offdiag_pairs if w2==(1-w)%p and (1-w)%p in mu_set)
    return dict(p=p,n=n,m=m, N=N, N_over_n=N/n, n_offdiag=len(offdiag_pairs),
                c_dist=dict(sorted(c_dist.items())),
                frac_antipodal=antip/max(len(offdiag_pairs),1),
                frac_inverse=inv/max(len(offdiag_pairs),1),
                frac_one_minus=one_minus/max(len(offdiag_pairs),1))

if __name__=="__main__":
    print("# Tangent-correlation structure: is Sol = {(w,w'): (1-w)/(1-w') in mu_n} explicit? (#407)\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'N':>5} {'N/n':>5} {'#offdiag':>8} | {'c_dist (fiber sizes)':>28} | {'%antip':>7} {'%inv':>6}")
    for n in [4,8,16,32,64]:
        cnt=0; k=2
        while cnt<3:
            p=k*n+1; k+=1
            if p>200000: break
            if (p-1)%n==0 and is_prime(p):
                # prefer p>n^2 (genuine subgroup, not whole group)
                if p < n*n: continue
                r=analyze(p,n)
                if r:
                    print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['N']:>5} {r['N_over_n']:>5.2f} "
                          f"{r['n_offdiag']:>8} | {str(r['c_dist']):>28} | "
                          f"{r['frac_antipodal']:>7.3f} {r['frac_inverse']:>6.3f}")
                    cnt+=1
    print("\nKEY: if c_dist is mostly {1:...,2:few} with %antip~1.0 => Sol = diagonal + antipodal involution")
    print("     (EXACT structure, house pin-able).  If c_dist has large fibers / %antip~0 => generic (wall).")
