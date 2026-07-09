#!/usr/bin/env python3
"""
probe_444_defect_hunt.py  (#444 SEAM A, TASK 3 -- refutation / non-vacuity)

The bijection (members<->lacunary) and the const<->coset / nonconst<->noncoset-defect equivalences
are EXACT identities (task1/task2). They are only NON-VACUOUS if a DEFECT (non-coset lacunary
subset / non-constant member) can actually occur. This script HUNTS for defects:

A non-coset lacunary subset of size a in mu_n (k=2 case) = a size-a set T whose
  prod_{t in T}(x-t) = x^a - alpha*x + c  with alpha != 0.
Equivalently: a degree-a binomial-ish trinomial x^a - alpha x + c that SPLITS COMPLETELY into
DISTINCT roots, ALL of which are n-th roots of unity, with alpha != 0.

We hunt by directly brute-enumerating ALL size-a lacunary subsets across MANY primes and indices,
and across SMALLER prize exponents too (a = n/4 fixed by task; also try a = n/2, a = 2 to see if
defects ever appear for ANY even a|n). We DO NOT restrict to prize-shape; we let index m=(p-1)/n
range freely and p range small so brute is cheap. If a defect appears at ANY (n,a,p), we then
re-run the bijection check at that prime to confirm member<->lacunary still matches on the defect.
"""
import itertools
from sympy import isprime, primitive_root

def primes_for(n, count, idx_min=2, pmin=None):
    """primes p>pmin with (p-1)%n==0 and index>=idx_min (no prize-shape constraint)."""
    p = (pmin or (n+1))
    p += (1 - p) % n if (p-1)%n else 0
    out=[]
    pp = n+1
    while len(out)<count:
        if pp> (pmin or 0) and isprime(pp) and (pp-1)%n==0 and (pp-1)//pp*0==0 and (pp-1)//n>=idx_min:
            out.append(pp)
        pp+=n
    return out

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r

def prod_coeffs(subset_vals, p):
    poly=[1]
    for t in subset_vals: poly=poly_mul(poly,[(-t)%p,1],p)
    return poly

def is_coset_idx(subset_idx, n, d):
    step=n//d; s=set(subset_idx)
    if len(s)!=d: return False
    for i0 in range(n):
        if set((i0+step*j)%n for j in range(d))==s: return True
    return False

def lacunary_brute(n, a, elts, p):
    """size-a subsets with coeff x^2..x^{a-1} of prod(x-t) all zero (k=2 lacunary)."""
    res=[]
    for Tidx in itertools.combinations(range(n),a):
        poly=prod_coeffs([elts[i] for i in Tidx],p)
        if all(poly[j]==0 for j in range(2,a)):
            res.append((tuple(sorted(Tidx)),poly))
    return res

def hunt(n, a, primes, label):
    print(f"\n--- HUNT n={n} a={a} ({label}) over {len(primes)} primes ---")
    total_defect=0
    for p in primes:
        elts=subgroup(n,p)
        lac=lacunary_brute(n,a,elts,p)
        nonc=[(T,poly) for (T,poly) in lac if not is_coset_idx(T,n,a)]
        # for k=2, non-coset <=> alpha!=0 <=> coeff x^1 (=poly[1]) != 0
        alpha_nonzero=[(T,poly) for (T,poly) in lac if poly[1]!=0]
        # sanity: non-coset set should equal alpha!=0 set
        assert set(T for T,_ in nonc)==set(T for T,_ in alpha_nonzero), \
            f"non-coset != alpha-nonzero at p={p}: {[T for T,_ in nonc]} vs {[T for T,_ in alpha_nonzero]}"
        if nonc:
            total_defect+=len(nonc)
            idx=(p-1)//n
            print(f"   p={p} idx={idx}: #lac={len(lac)} #NONCOSET(DEFECT)={len(nonc)} "
                  f"example T={nonc[0][0]} prod-coeffs(low->high)={nonc[0][1]}")
    if total_defect==0:
        print(f"   NO non-coset lacunary subset found over all {len(primes)} primes "
              f"(every size-{a} lacunary set is a mu_{a}-coset).")
    return total_defect

if __name__=="__main__":
    print("="*100)
    print("TASK 3: DEFECT HUNT -- does a non-coset lacunary subset (non-constant member) EVER exist?")
    print("="*100)
    # n=16, a=n/4=4 (the task's clean case), MANY primes incl. small indices
    hunt(16, 4, primes_for(16, 60, idx_min=2, pmin=16), "a=n/4, idx>=2, small primes")
    hunt(16, 4, primes_for(16, 40, idx_min=2, pmin=65000), "a=n/4, prize-window primes")
    # also try OTHER even a|16 to see if defects appear for any a
    hunt(16, 2, primes_for(16, 60, idx_min=2, pmin=16), "a=2 (even, a|16)")
    hunt(16, 8, primes_for(16, 40, idx_min=2, pmin=16), "a=8=n/2 (even, a|16)")
    # n=8, a=2 cheap exhaustive over very many primes
    hunt(8, 2, primes_for(8, 120, idx_min=1, pmin=8), "n=8 a=2 idx>=1 wide")
    # n=12 (not 2-power but lets a=4|12 with extra structure) -- probe whether 2-power-ness matters
    # (12 is allowed: domain = order-12 subgroup; a=4)
    hunt(12, 4, primes_for(12, 60, idx_min=2, pmin=12), "n=12 a=4 (non-2-power control)")
