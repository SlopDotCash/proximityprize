#!/usr/bin/env python3
"""
SYZ55 -- the GENERATOR-GAP SPLIT of the balanced-interior residual, with per-candidate-scalar
forensics of WHY the big-gap (constant-syzygy) witnesses lift harmlessly at large p.

Context (predecessors):
  * SYZ44  degree-sum law delta1+delta2 = a+b+c =: S, minimal generator delta1 <= delta2.
  * SYZ53  imbalance iota = floor((delta2-delta1)/2); iota<=1 <=> gap g:=delta2-delta1 <= 3.
  * SYZ50/52  the band-realizable (4,4,4),t=2 interior witnesses (mu14 subset F_p) are genuine
    CONSTANT-syzygy witnesses: W_BC = R*W_AC + c*W_AB with R,c in F_p constants, i.e. the three
    band polynomials are F-linearly DEPENDENT.  A constant syzygy is a DEGREE-0 syzygy => delta1=0
    => gap g = S = 12 (the maximal gap).  So these witnesses are the gap>=4 branch, NOT gap<=3.
  * SYZ53-pscaling  those big-gap witnesses STILL produce only max mca-bad = 3 (generic pencil
    floor) at every large prime, deep below ceiling sum(n-s_i)=12.  VERDICT: collapse.

This probe does the two things SYZ55 needs on top of that verdict:

  (1) THE KILLING MECHANISM (forensics).  For a fixed constant-syzygy witness at p ~ 1e6, take the
      EXACT bad-z set of a degenerate stack (SYZ53 exact_badz) and attribute EACH bad z to the
      size-s subset(s) S that made the line s-close.  Classify every candidate:
        - STRUCTURAL: S is one of the three cores (or forced by the constant syzygy) -> present at
          ALL primes (the generic pencil floor).
        - ACCIDENTAL: S is a non-core subset whose parity vectors a0,a1 are only *coincidentally*
          parallel mod p -> present with probability ~1/p, GONE at large p.
      We show the small-p over-budget excess is entirely ACCIDENTAL and the large-p survivors are
      entirely STRUCTURAL (<= 3).  That is the per-scalar mechanism.

  (2) THE SPLIT COVERAGE.  Compute, per realizable witness, the minimal syzygy degree delta1 (hence
      gap g = S - 2*delta1), over the band-realizable interior configs.  Question: is every
      realizable witness either gap<=3 (near-balance, iota<=1) OR a low-degree-syzygy (gap>=4) one
      whose lift is floor-bounded?  Are there MIDDLE-gap (g in {4..S-1}, delta1 in {1..(S-4)/2})
      realizable witnesses that are neither near-balance nor fully constant-dependent?
"""
import itertools, random, sys, os, collections
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached,
    A_C_basis, deficiency)
from probe_syz52_witness_lift import (find_witnesses, build_interp_tensor, _agr_masks, cores_of)
from probe_syz53_p_scaling import (subset_parity, exact_badz, next_prime_1modn, is_prime)

# ------------------------------------------------------------------ minimal syzygy degree delta1
def poly_from_roots(roots, p):
    """monic polynomial (low->high coeff) with the given roots in F_p."""
    c = [1]
    for r in roots:
        nc = [0]*(len(c)+1)
        for i, ci in enumerate(c):
            nc[i]   = (nc[i]   - r*ci) % p
            nc[i+1] = (nc[i+1] + ci)   % p
        c = nc
    return c

def min_syzygy_degree(polys, p, dmax=None):
    """Smallest d such that (A0,A1,A2) with deg Ai <= d and sum Ai*fi = 0 has a nonzero solution.
    Returns (delta1, nullity_at_delta1).  Pure linear algebra over F_p."""
    degs = [len(f)-1 for f in polys]
    S = sum(degs)
    if dmax is None: dmax = S
    for d in range(0, dmax+1):
        # unknown coeff vector: 3 blocks each of length d+1.  Product Ai*fi has degree <= d+deg fi;
        # collect all product-coefficient equations = 0.  Build matrix rows = coeff index.
        ncols = 3*(d+1)
        maxdeg = d + max(degs)
        rows = [[0]*ncols for _ in range(maxdeg+1)]
        col = 0
        for bi, f in enumerate(polys):
            for j in range(d+1):            # coeff of x^j in Ai
                for ei, fe in enumerate(f): # f has coeff fe at x^ei
                    rows[j+ei][col] = (rows[j+ei][col] + fe) % p
                col += 1
        rank, null = rref_rank_nullbasis(rows, ncols, p)
        if null:
            return d, len(null)
    return dmax+1, 0

# ------------------------------------------------------------------ (1) forensic attribution
def forensic_stack(mu, k, s, p, cores, seed, trials, target_excess_only=True):
    """Find a degenerate stack and return its EXACT bad-z set with per-z subset attribution."""
    n=len(mu)
    Db=dual_basis_cached(mu,k,p)
    AC=[A_C_basis(Db,C,n,p) for C in cores]
    rng=random.Random(seed)
    subs,Hs = subset_parity(mu,k,s,p)
    core_sets=[frozenset(c) for c in cores]
    best=None
    for _ in range(trials):
        zs=rng.sample(range(1,p),3)
        rowsM=[]
        for i in range(3):
            for v in AC[i]:
                rowsM.append([v[j]%p for j in range(n)]+[(zs[i]*v[j])%p for j in range(n)])
        r,null=rref_rank_nullbasis(rowsM,2*n,p)
        if not null: continue
        u=[0]*(2*n)
        for b in null:
            c=rng.randrange(p)
            for j in range(2*n): u[j]=(u[j]+c*b[j])%p
        u0,u1=u[:n],u[n:]
        if all(x==0 for x in u1): continue
        bad,inf,mca,wf=exact_badz(u0,u1,mu,k,s,p)
        if mca: continue
        # attribute: for each bad z, which subsets S make u0+z u1 s-close (parity vanish)
        attrib={}
        for z in bad:
            hits=[]
            for S,H in zip(subs,Hs):
                ok=True
                for h in H:
                    acc=0
                    for idx,j in enumerate(S):
                        acc=(acc+int(h[idx])*((u0[j]+z*u1[j])%p))%p
                    if acc%p!=0: ok=False; break
                if ok: hits.append(frozenset(S))
            # structural iff some hit subset is (contained in / equals) a core
            structural=any(any(hs<=cs or cs<=hs for cs in core_sets) for hs in hits)
            attrib[z]=dict(nsub=len(hits), structural=structural,
                           core_hit=any(hs in core_sets for hs in hits))
        if best is None or len(bad)>len(best[0]):
            best=(bad,attrib,u0,u1)
        if len(bad)>=4:      # found an at-or-above-floor stack; stop
            break
    return best

def run_forensics():
    n,k,a,t=14,7,4,2; s=a+a+t
    print("="*92); print("(1) KILLING-MECHANISM FORENSICS  n=14 k=7 (4,4,4) t=2 s=10  ceiling=3(n-s)=12")
    print("="*92)
    for tgt in [29, 1000003]:
        p=next_prime_1modn(tgt,n)
        mu,wit=find_witnesses(p,n,a)
        if not wit:
            print(f"  p={p}: no witness"); continue
        # pick a constant-syzygy witness; confirm delta1=0 via its three band polynomials
        AC,BC,AB,T,R=wit[0]
        polys=[poly_from_roots([mu[i] for i in idx],p) for idx in (AC,BC,AB)]
        d1,nul=min_syzygy_degree(polys,p)
        S=sum(len(f)-1 for f in polys); gap=S-2*d1
        cores=cores_of(AC,BC,AB,T)
        res=forensic_stack(mu,k,s,p,cores,seed=7,trials=1500)
        print(f"\n  p={p} (log2={np.log2(p):.1f})  witness #0  band degs={[len(f)-1 for f in polys]} "
              f"S={S}  delta1={d1} (nullity {nul})  gap g=S-2*delta1={gap}  [iota=floor(g/2)={gap//2}]")
        if res is None:
            print("    no degenerate stack found"); continue
        bad,attrib,u0,u1=res
        nstruct=sum(1 for z in bad if attrib[z]['structural'])
        nacc=len(bad)-nstruct
        print(f"    EXACT bad-z on a degenerate stack: |bad|={len(bad)}  "
              f"(structural={nstruct}, accidental={nacc})  ceiling=12")
        for z in sorted(bad):
            A=attrib[z]
            tag="STRUCTURAL(core)" if A['core_hit'] else ("STRUCTURAL" if A['structural'] else "ACCIDENTAL")
            print(f"      z={z:<8}  #closing-subsets={A['nsub']:<3}  {tag}")

# ------------------------------------------------------------------ (2) split coverage / middle-gap
def run_split_coverage():
    print("\n"+"="*92)
    print("(2) SPLIT COVERAGE: per-witness minimal syzygy degree delta1 (=> gap g=S-2*delta1)")
    print("    gap<=3 : near-balance branch (iota<=1).   gap>=4 : low-syzygy branch.")
    print("    MIDDLE = gap in {4..S-1} with delta1 in {1..}, i.e. NOT constant (delta1=0) NOR near-balance.")
    print("="*92)
    configs=[(14,7,4,2),(16,8,4,3),(18,9,5,3),(20,10,5,4),(22,11,6,4)]
    for (n,k,a,t) in configs:
        s=a+a+t; S=3*a
        p=next_prime_1modn(100003,n)
        mu,wit=find_witnesses(p,n,a,max_wit=150)
        if not wit:
            print(f"  n={n} (a,a,a)=({a},{a},{a}) t={t}: syzygy-empty on domain"); continue
        buckets=collections.Counter()  # (delta1, gap) -> count
        d1min=99
        for (AC,BC,AB,T,R) in wit:
            polys=[poly_from_roots([mu[i] for i in idx],p) for idx in (AC,BC,AB)]
            d1,_=min_syzygy_degree(polys,p,dmax=S)
            gap=S-2*d1
            buckets[(d1,gap)]+=1
            d1min=min(d1min,d1)
        print(f"\n  n={n} k={k} (a,a,a)=({a},{a},{a}) t={t}  S={S}  #wit={len(wit)}  p={p}")
        for (d1,gap),c in sorted(buckets.items()):
            branch="near-balance(g<=3)" if gap<=3 else ("constant-dep(delta1=0)" if d1==0 else "MIDDLE")
            print(f"     delta1={d1:<2} gap={gap:<3} : {c:<5} witnesses   [{branch}]")
        mids=sum(c for (d1,gap),c in buckets.items() if gap>=4 and d1>=1)
        print(f"     --> MIDDLE-gap (g>=4, delta1>=1) realizable witnesses: {mids}")

if __name__=="__main__":
    run_forensics()
    run_split_coverage()
    print("\nDONE.")
