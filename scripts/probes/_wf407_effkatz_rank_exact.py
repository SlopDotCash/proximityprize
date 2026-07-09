#!/usr/bin/env python3
"""
[#407 effkatz] EXACT conductor (generic rank) of b -> eta_b, via the algebraic recurrence.

eta_b = sum_{x in mu_n} zeta^{b x},  zeta = primitive p-th root of unity.
As a sequence in b, eta_b = sum over the n group elements x of (zeta^x)^b: a sum of n geometric
progressions with DISTINCT ratios zeta^x (x in mu_n, all distinct mod p, all != 1 since x in F_p^x
and x ranges over n distinct residues; ratios zeta^x are n distinct p-th roots of unity).
=> the minimal linear recurrence order of (eta_b)_b is EXACTLY n  (char poly prod_{x in mu_n}(T-zeta^x),
n distinct roots, all coefficients nonzero generically) => the GENERIC RANK of the family = n EXACTLY.

This is the conductor of incarnation (I) (additive-FT sheaf): c(F) = Theta(n).  We confirm rank==n
EXACTLY over the integers/exact arithmetic (Smith-normal-form-free: just count distinct ratios),
removing the floating SVD artifact.  Then we state the prize-scale verdict.
"""
import math

def primitive_root(p):
    if p==2: return 1
    pm1=p-1; f=set(); d=pm1; k=2
    while k*k<=d:
        while d%k==0: f.add(k); d//=k
        k+=1
    if d>1: f.add(d)
    for g in range(2,p):
        if all(pow(g,pm1//q,p)!=1 for q in f): return g
    return None

def subgroup(p,n):
    g=primitive_root(p); m=(p-1)//n; gen=pow(g,m,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*gen)%p
    return S

def exact_generic_rank(p,n):
    """generic rank = number of DISTINCT ratios zeta^x = number of distinct x mod p in mu_n = n."""
    S=subgroup(p,n)
    distinct = len(set(S))
    # the recurrence order is the number of distinct nonzero ratios; all x in mu_n are nonzero & distinct
    return distinct

print(f"{'p':>7} {'m':>7} {'n':>6} {'rank':>6} {'==n?':>5} {'n/sqrt(p)':>10} {'1/m':>9} {'n/sqrt(p)<1/m?':>15}")
bad=0
for p in [13,29,37,41,53,61,73,89,97,101,113,127,257,521,1031,2053,4099,8209,65537]:
    pm1=p-1
    i=1; pairs=[]
    while i*i<=pm1:
        if pm1%i==0: pairs.append((i,pm1//i)); pairs.append((pm1//i,i))
        i+=1
    for (m,n) in sorted(set(pairs)):
        if n<2 or m<2: continue
        r=exact_generic_rank(p,n)
        ok = (r==n)
        if not ok: bad+=1
        cond_feed = n/math.sqrt(p)
        invm = 1.0/m
        # only print a representative subset to keep it readable
        if n<=8 or m<=8 or p>=2053:
            print(f"{p:>7} {m:>7} {n:>6} {r:>6} {str(ok):>5} {cond_feed:>10.4f} {invm:>9.5f} "
                  f"{str(cond_feed<invm):>15}")
print(f"\nrank != n cases: {bad}  (0 means conductor == n EXACTLY, always)")

print("\n"+"="*70)
print("DECISIVE PRIZE-SCALE INEQUALITY")
print("="*70)
print("The comment: to beat 1/m you'd need conductor < sqrt(n/m).")
print("With conductor = n exactly, the threshold  cond*p^{-1/2} < 1/m  becomes")
print("   n/sqrt(p) < 1/m   <=>   n*m < sqrt(p)   <=>   (p-1) < sqrt(p)  -- FALSE for all p>=2.")
print("So the additive-FT Deligne bound is feeding cond*p^{-1/2}=n/sqrt(p)=(p-1)/(m*sqrt(p)),")
print("and  (p-1)/sqrt(p) ~ sqrt(p) >> 1  -- the bound is ALWAYS VACUOUS pointwise (>1).")
print()
# prize numbers
import math
print("Prize instance n=2^32, m=2^128, p=n*m+1~2^160:")
n=2.0**32; m=2.0**128; p=n*m
print(f"  n/sqrt(p) = {n/math.sqrt(p):.3e}  (=2^{math.log2(n/math.sqrt(p)):.1f})")
print(f"  1/m       = {1/m:.3e}  (=2^{-128})")
print(f"  need conductor < sqrt(n/m) = 2^{0.5*math.log2(n/m):.1f} = 2^-48  -- IMPOSSIBLE (cond=n=2^32>=1)")
print(f"  ACTUAL cond*p^-1/2 = n/sqrt(p) = 2^{math.log2(n/math.sqrt(p)):.1f}  vs needed 2^-128: short by 2^{math.log2(n/math.sqrt(p))+128:.0f}")
