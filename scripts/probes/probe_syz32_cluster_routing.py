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
  (3) LIFT TEST over SAMPLED pencil stacks: complete list-decode of every finite line point and
      of the direction z=inf, reporting separately
        * CLOSE finite scalars (closeness only),
        * whether z=inf is close (a projective point; never added to the finite-scalar count),
        * MCA-BAD finite scalars in the ArkLib `mcaEvent` sense: SOME close codeword of
          u0+z*u1 has an agreement set on which (u0,u1) is NOT jointly explained.
      The nonjointness test is per scalar, on that scalar's own witness set.  A whole-stack
      correlated-agreement test (some row codewords sharing a joint agreement set of size >= s
      somewhere) does NOT exclude a different, nonjoint close witness at a given scalar, so it
      is not an MCA filter.  It matches the different stack-level `corrAgree` notion of
      ArkLib `MCABadScalarSpreadBridge.mcaBad`; the probe reports that count separately and
      labels it as such.  Regression fixture (audit 2026-10-28 finding L124, reusing L122):
      F17, n16, k8, s11, u0=[0]*11+[1,0,0,0,0], u1=[0]*11+[4,12,9,1,4] has global correlated
      agreement on {0..10}, yet z=1 is MCA-bad via prod_(a=0..6)(X-a) on {0..6,11..15}.
      Sampled counts are evidence about the sampled stacks only, not a certificate for the strip.
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached, A_C_basis,
    deficiency, sum_excess)
from probe_syz28_verify_classification import (build_interp_mats, close_codewords,
    pair_joint_on)

# The SYZ31 near-duplicate-triple crack (n=16, k=8, four size-11 cores).
CRACK=[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
       [0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15],
       [0, 1, 2, 3, 4, 6, 11, 12, 13, 14, 15],
       [0, 1, 2, 3, 5, 6, 11, 12, 13, 14, 15]]
n,k,s,p=16,8,11,17
alpha=list(range(n))
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

def agreement_sets(w):
    """Full agreement sets (>= s) of the distinct close codewords of w (complete decoder)."""
    return set(tuple(sorted(A)) for A in close_codewords(w,mats,n,k,s,p).values())

def is_close(w): return len(agreement_sets(w))>0

def global_corr_agree(u0,u1):
    """STACK-LEVEL correlated agreement (ArkLib `MCABadScalarSpreadBridge.corrAgree`): some set
    of size >= s on which BOTH rows agree with codewords.  This is NOT the per-scalar MCA
    condition: a stack can satisfy it and still have MCA-bad scalars whose own witness sets are
    not jointly explained (fixture in the module docstring)."""
    A0=agreement_sets(u0); A1=agreement_sets(u1)
    for a in A0:
        for b in A1:
            if len(set(a)&set(b))>=s: return True
    return False

def lift_counts(u0,u1):
    """Per-stack classification: close finite scalars, inf closeness, per-scalar MCA-bad finite
    scalars (existential nonjoint witness over ALL distinct close codewords), and the separate
    stack-level correlated-agreement flag."""
    close=[]; mca_bad=[]
    for z in range(p):
        cw=close_codewords([(u0[j]+z*u1[j])%p for j in range(n)],mats,n,k,s,p)
        if not cw: continue
        close.append(z)
        if any(not pair_joint_on(A,u0,u1,k,p) for A in cw.values()): mca_bad.append(z)
    return dict(close=close, inf_close=is_close(u1), mca_bad=mca_bad,
                global_corr=global_corr_agree(u0,u1))

def pencil_stack(AC,zs):
    """Random pencil stack (u0,u1) for the cores' A_C bases and pencil scalars zs, or None."""
    rows=[]
    for i in range(len(AC)):
        for v in AC[i]:
            rows.append([v[j]%p for j in range(n)]+[(zs[i]*v[j])%p for j in range(n)])
    r,null=rref_rank_nullbasis(rows,2*n,p)
    if not null: return None
    u=[0]*(2*n)
    for b in null:
        c=random.randrange(p)
        for j in range(2*n): u[j]=(u[j]+c*b[j])%p
    u0,u1=u[:n],u[n:]
    if all(x==0 for x in u1): return None
    return u0,u1

def main(merge_trials=4000, lift_trials=4000):
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
          "->","FIELD-INDEPENDENT (genuine matroid deficiency)" if all(x>0 for x in ds)
          else "accident")

    # ---------- (2) verify the merge: cluster cores share one local pair ----------
    print("\n(2) merge verification: do near-duplicate cluster cores carry the SAME local codeword?")
    Db=dual_basis_cached(alpha,k,p)
    AC=[A_C_basis(Db,C,n,p) for C in CRACK]
    random.seed(7)
    merge_confirmed=0; merge_tested=0; both_exist=0
    for _ in range(merge_trials):
        st=pencil_stack(AC,random.sample(range(1,p),4))
        if st is None: continue
        u0,u1=st
        # for each cluster core, does u0 decode on it?  if two do, are the codewords equal?
        decs=[decoded_on(u0,CRACK[i]) for i in (1,2,3)]
        present=[d for d in decs if d is not None]
        if len(present)>=2:
            both_exist+=1
            merge_tested+=1
            # all present decodings must be the SAME global codeword (RS uniqueness, >=k overlap)
            if all(d==present[0] for d in present): merge_confirmed+=1
    print(f"    stacks with >=2 cluster cores decoding: {both_exist}; "
          f"all-agree (single merged pencil): {merge_confirmed}/{merge_tested}")
    print("    => cluster is YIELD-DEGENERATE: its three near-dup cores donate ONE pencil, not three"
          if merge_tested and merge_confirmed==merge_tested else "    => MERGE FAILED, investigate")

    # ---------- (3) lift test: close vs per-scalar MCA-bad counts ----------
    print("\n(3) lift test over SAMPLED pencil stacks: complete list-decode; closeness and")
    print("    per-scalar MCA badness (existential nonjoint witness) reported separately")
    random.seed(3)
    stacks=0; inf_close=0; corr_stacks=0
    max_close=0; max_bad=0; best=None; max_bad_noncorr=0
    for trial in range(lift_trials):
        st=pencil_stack(AC,random.sample(range(1,p),4))
        if st is None: continue
        c=lift_counts(*st)
        stacks+=1
        inf_close+=c['inf_close']; corr_stacks+=c['global_corr']
        max_close=max(max_close,len(c['close']))
        if len(c['mca_bad'])>max_bad: max_bad=len(c['mca_bad']); best=c
        if not c['global_corr']: max_bad_noncorr=max(max_bad_noncorr,len(c['mca_bad']))
    print(f"    pencil stacks sampled: {stacks}")
    print(f"    max CLOSE finite scalars (closeness only, no MCA filter): {max_close}")
    print(f"    stacks whose direction z=inf is close (projective; not a finite scalar): {inf_close}")
    print(f"    max MCA-BAD finite scalars (per-scalar existential nonjoint witness): {max_bad}")
    if best: print(f"    achieved with close={best['close']}  mca_bad={best['mca_bad']}")
    print(f"    stacks with STACK-LEVEL correlated agreement (MCABadScalarSpreadBridge.corrAgree;"
          f" not an MCA filter): {corr_stacks}")
    print(f"    max MCA-bad finite scalars among stacks WITHOUT stack-level correlated agreement:"
          f" {max_bad_noncorr}")
    print("    merged pool (n-s0)+(n-|Uc|)=5+4=9  (cluster union |C1uC2uC3|=12);"
          "  SYZ22 budget n-1=15;  falsify needs > n=16 finite MCA-bad scalars")
    print("    VERDICT (sampled stacks only; not a certificate for the whole strip):",
          "no sampled stack exceeds the SYZ22 budget n-1 in MCA-bad finite scalars"
          if max_bad<=15 else ("AT BUDGET EDGE" if max_bad<=16 else "OVER BUDGET - INVESTIGATE"))

if __name__=="__main__":
    main()
