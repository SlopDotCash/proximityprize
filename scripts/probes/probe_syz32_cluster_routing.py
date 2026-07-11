#!/usr/bin/env python3
"""
SYZ32: cluster-routing assembly — the decisive lift test of the SYZ31 near-duplicate crack.

SYZ31 exhibited a D=4 over-budget band full cover `syz31Crack` (n=16, k=8, all cores size 11)
whose two-block cross-intersection floor FAILS: the matroid rank-deficiency is d=1,
field-independent.  That refuted the *conjectured* raw floor but left the routing question open:
does the crack FALSIFY the strip, or is it stack-vacuous?

The reconciliation (the SYZ20 merge argument): cores C1,C2,C3 pairwise overlap 10 >= k = 8.  Two
RS[16,8] local codewords agreeing on >= k = 8 points are EQUAL (RS uniqueness / MDS distance).
So on the STACK, any local codeword pair (v0,v1) explaining the line on Ci also explains it on Cj
wherever they overlap in >= k points -- hence C1,C2,C3 carry the SAME local pair and the SAME
pencil.  The matroid index set has D=4 distinct cores (rank-deficiency is real), but the physical
lift merges the near-duplicate cluster into ONE pencil: the stack behaves like the merged D=2
family {C0, cluster}.  Prediction: max mca-bad count is FAR under the SYZ22 budget n-1 = 15 --
it should saturate the MERGED pencil pool (n-s0)+(n-|Uc|) = 5+4 = 9, not the naive
4*(n-s) = 20 nor even the strict-interior cap.

This probe:
  (1) confirms the matroid d=1, field-independent (reproduces SYZ31);
  (2) VERIFIES THE MERGE numerically: on every pencil stack where local pairs exist for the
      near-duplicate cluster cores, those pairs COINCIDE (same codeword) -- so the cluster
      donates a single pencil;
  (3) LIFT TEST: exhaustive mca-filtered list-decode of all pencil line points, max bad-scalar
      count -- the decisive check that the crack is under-budget.
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached, A_C_basis,
    deficiency, sum_excess)
from probe_syz28_verify_classification import build_interp_mats

# The SYZ31 near-duplicate-triple crack (n=16, k=8, four size-11 cores).
CRACK=[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
       [0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15],
       [0, 1, 2, 3, 4, 6, 11, 12, 13, 14, 15],
       [0, 1, 2, 3, 5, 6, 11, 12, 13, 14, 15]]
n,k,s,p=16,8,11,17
alpha=list(range(n))

print("="*84)
print("SYZ32: cluster-routing assembly -- lift test of the SYZ31 near-duplicate crack")
print("="*84)

# ---------- (1) matroid deficiency, field-independent (reproduce SYZ31) ----------
S=[set(c) for c in CRACK]
print("\n(1) matroid deficiency (reproduce SYZ31)")
print("    core sizes:",[len(c) for c in CRACK])
print("    cluster {1,2,3} pairwise overlaps:",
      sorted(len(S[a]&S[b]) for a,b in itertools.combinations([1,2,3],2)),"(all 10 > k=8)")
ds=[deficiency(alpha,k,pp,CRACK)[0] for pp in (101,1009,65537,1000003,2147483647)]
print("    d over primes {101,1009,65537,1e6+3,2^31-1}:",ds,
      "->","FIELD-INDEPENDENT (genuine matroid deficiency)" if all(x>0 for x in ds) else "accident")

# ---------- (2) verify the merge: cluster cores share one local pair ----------
print("\n(2) merge verification: do near-duplicate cluster cores carry the SAME local codeword?")
mats=build_interp_mats(n,k,s,p)

def local_pairs(w):
    """all deg<k polynomials (as full n-vectors) agreeing with w on some core-sized (>=s) set,
    keyed by the agreement set; returns dict agr_set(tuple)->decoded n-vector."""
    outs={}
    for T,M in mats:
        vals=[w[t] for t in T]
        dec=[sum(a*b for a,b in zip(M[j],vals))%p for j in range(n)]
        agr=tuple(j for j in range(n) if dec[j]==w[j]%p)
        if len(agr)>=s: outs[agr]=dec
    return outs

def decoded_on(w,C):
    """the (unique if it exists) deg<k codeword agreeing with w on all of core C (|C|=s>=k)."""
    Cl=sorted(C)
    # interpolate through the first k points of C, then check agreement on the rest of C
    T=Cl[:k]
    # build Lagrange interp matrix for these k nodes evaluated at all n points
    for TT,M in mats:
        if list(TT)==T:
            vals=[w[t] for t in T]
            dec=[sum(a*b for a,b in zip(M[j],vals))%p for j in range(n)]
            if all(dec[j]==w[j]%p for j in Cl): return tuple(dec)
            return None
    return None

Db=dual_basis_cached(alpha,k,p)
AC=[A_C_basis(Db,C,n,p) for C in CRACK]
random.seed(7)
merge_confirmed=0; merge_tested=0; both_exist=0
for _ in range(4000):
    zs=random.sample(range(1,p),4)
    rows=[]
    for i in range(4):
        for v in AC[i]:
            rows.append([v[j]%p for j in range(n)]+[(zs[i]*v[j])%p for j in range(n)])
    r,null=rref_rank_nullbasis(rows,2*n,p)
    if not null: continue
    u=[0]*(2*n)
    for b in null:
        c=random.randrange(p)
        for j in range(2*n): u[j]=(u[j]+c*b[j])%p
    u0,u1=u[:n],u[n:]
    if all(x==0 for x in u1): continue
    # for each cluster core, does u0 decode on it?  if two do, are the codewords equal off-core?
    decs=[decoded_on(u0,CRACK[i]) for i in (1,2,3)]
    present=[d for d in decs if d is not None]
    if len(present)>=2:
        both_exist+=1
        merge_tested+=1
        # all present decodings must be the SAME global codeword (RS uniqueness on >=k overlap)
        if all(d==present[0] for d in present): merge_confirmed+=1
print(f"    stacks with >=2 cluster cores decoding: {both_exist}; "
      f"all-agree (single merged pencil): {merge_confirmed}/{merge_tested}")
print("    => cluster is YIELD-DEGENERATE: its three near-dup cores donate ONE pencil, not three"
      if merge_tested and merge_confirmed==merge_tested else "    => MERGE FAILED, investigate")

# ---------- (3) lift test: max mca-bad scalar count ----------
print("\n(3) lift test: mca-filtered list-decode, max bad-scalar count over pencil stacks")

def agreement_sets(w):
    outs=set()
    for T,M in mats:
        vals=[w[t] for t in T]
        agr=[j for j in range(n) if sum(a*b for a,b in zip(M[j],vals))%p==w[j]%p]
        if len(agr)>=s: outs.add(tuple(agr))
    return outs

def is_close(w): return len(agreement_sets(w))>0

def mca_holds(u0,u1):
    A0=agreement_sets(u0); A1=agreement_sets(u1)
    for a in A0:
        for b in A1:
            if len(set(a)&set(b))>=s: return True
    return False

random.seed(3)
maxbad=0; best=None; stacks=0
maxbad_raw=0; stacks_raw=0
for trial in range(4000):
    zs=random.sample(range(1,p),4)
    rows=[]
    for i in range(4):
        for v in AC[i]:
            rows.append([v[j]%p for j in range(n)]+[(zs[i]*v[j])%p for j in range(n)])
    r,null=rref_rank_nullbasis(rows,2*n,p)
    if not null: continue
    u=[0]*(2*n)
    for b in null:
        c=random.randrange(p)
        for j in range(2*n): u[j]=(u[j]+c*b[j])%p
    u0,u1=u[:n],u[n:]
    if all(x==0 for x in u1): continue
    # raw pool: bad scalars ignoring the mca filter (measures the pencil pool the stack realizes)
    bad_raw=[z for z in range(p) if is_close([(u0[j]+z*u1[j])%p for j in range(n)])]
    if is_close(u1): bad_raw.append('inf')
    stacks_raw+=1
    if len(bad_raw)>maxbad_raw: maxbad_raw=len(bad_raw)
    if mca_holds(u0,u1): continue    # correlated agreement => not mca-bad
    stacks+=1
    if len(bad_raw)>maxbad: maxbad=len(bad_raw); best=(zs,bad_raw)
print(f"    pencil stacks sampled: {stacks_raw};  max RAW bad scalars (pool proxy): {maxbad_raw}")
print(f"    non-correlated (genuine mca-bad) pencil stacks: {stacks}")
print(f"    max mca-bad scalars: {maxbad}")
if best: print(f"    achieved at z_i={best[0]}  bad={best[1]}")
print(f"    merged pool (n-s0)+(n-|Uc|)=5+4=9  (cluster union |C1uC2uC3|=12);  SYZ22 budget n-1=15;  falsify needs > n=16")
print("    VERDICT:",
      "UNDER-BUDGET -> crack is STACK-VACUOUS (matroid-real, merged D=2 physics); strip SAFE"
      if maxbad<=15 else ("AT BUDGET EDGE" if maxbad<=16 else "OVER BUDGET - INVESTIGATE"))
