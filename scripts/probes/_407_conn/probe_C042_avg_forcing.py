#!/usr/bin/env python3
"""
C042 part 3: the FORCING argument (decides the verdict).
  Identity (exact, sum over all nonzero dilates h):
     sum_{h in F_q*} |S0 cap h S0| = sum_{a,b in S0, a,b!=0} #{h: h a = b}
                                    = |S0\{0}|^2          (each (a,b) has unique h=b/a)
     [if 0 in S0 it contributes |S0| extra fixed points; handle separately]
  Hence  AVG_{h} |S0 cap h S0| = |S0\{0}|^2 / (q-1)  EXACTLY.
  So Conj-1.12 spreading |S0| >= q/10  =>  AVG_h intersection >= (q/10)^2/(q-1) ~ q/100.
  The cross-parity dilate is the SINGLE fixed value h0 = -g; you do not get to choose it to
  minimize.  The empirical finding (part 2): h0=-g sits at the ~99th percentile (near MAX),
  so |S0 cap (-g)S0| >= AVG ~ q/100 = Theta(q) whenever Conj 1.12 holds.
  => "large |S0| (spread)" and "small |S0 cap (-g)S0| (thin)" are CONTRADICTORY:
     you literally cannot have a constant-fraction-of-q image be multiplicatively thin under
     a fixed near-worst dilate.  The "dual halves" are ANTAGONISTIC, both = |S0|/sum-product.
"""
import math, random
from itertools import combinations
def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s
def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None
def find_prime(n, beta):
    lo=int(n**beta); p = lo - (lo % n) + 1
    if p<lo: p+=n
    for _ in range(400000):
        if is_prime(p): return p
        p+=n
    return None
def subgroup(p, n):
    g0=gen_Fp_star(p); gen=pow(g0,(p-1)//n,p)
    return [pow(gen,i,p) for i in range(n)], g0
def subsetsum_image_full(mu,p):
    reach={0}
    for x in mu: reach |= {(v+x)%p for v in reach}
    return reach

print("="*100)
print("(C) EXACT averaging identity:  AVG_{h in F_q*} |S0 cap hS0| = |S0\\{0}|^2/(q-1)")
print("    (verify on full dilate-sweep for small q), then the q/100 forcing.")
print("="*100)
for (n,beta) in [(8,4.0),(8,4.5),(16,4.0)]:
    p=find_prime(n,beta)
    mu,g0=subgroup(p,n)
    S0=subsetsum_image_full(mu,p)
    Snz=S0-{0}
    # exact full sweep over h in F_q* of |S0 cap hS0|
    Sset=S0
    tot=0
    if p<=70000:   # full sweep feasible
        for h in range(1,p):
            tot+=len({(h*v)%p for v in Sset} & Sset)
        avg=tot/(p-1)
    else:
        # sample
        samp=2000; s=0
        for _ in range(samp):
            h=random.randrange(1,p); s+=len({(h*v)%p for v in Sset} & Sset)
        avg=s/samp
    pred=len(Snz)**2/(p-1)
    pred_with0 = (len(Snz)**2 + (1 if 0 in S0 else 0)*(p-1))/(p-1)  # 0 is fixed by all h
    print(f"  n={n} q={p}: |S0|={len(S0)} (0 in S0: {0 in S0})  AVG_h={avg:.4f}  pred |Snz|^2/(q-1)={pred:.4f}  pred+0fix={pred_with0:.4f}")

print()
print("="*100)
print("(D) MERSENNE EXTREME (the claim's 'worst defect'): S0 = ALL of F_q => |S0 cap hS0| = q for")
print("    EVERY h.  Confirmed structurally (univ intersect anything = univ).  The in-tree")
print("    sumsetDistinct_signedPowers_eq_univ gives S0 = univ for q=2^p-1, so int = q (max).")
print("    This is consistent BUT it is the WORST case for the floor, not a good one.")
print("="*100)
# n=32 q=n^4 had fill=1 already; show -g intersection = q there
p=find_prime(32,4.0); mu,g0=subgroup(p,32); S0=subsetsum_image_full(mu,p)
negg=(p-g0)%p
gg=len({(negg*v)%p for v in S0} & S0)
print(f"  n=32 q={p}: |S0|={len(S0)} fill={len(S0)/p:.4f}  |S0 cap (-g)S0|={gg}  (= q means worst)")
print()
print("VERDICT LOGIC:")
print("  * IDENTITY #defects = |S0 cap (-g)S0| : TRUE but tautological (re-expression).")
print("  * Conj 1.12 (|S0|>=q/10) => AVG_h int = |S0|^2/(q-1) >= q/100 = Theta(q).")
print("  * cross-parity dilate -g is FIXED and empirically ~99th percentile (>= avg),")
print("    so spreading FORCES |S0 cap (-g)S0| = Theta(q): NOT a usable small floor.")
print("  * => the two 'dual halves' are ANTAGONISTIC, both controlled by |S0| / sum-product")
print("    expansion of the subset-sum image = the BGK / sum-product wall.  No new lever.")
