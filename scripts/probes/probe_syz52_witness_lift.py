#!/usr/bin/env python3
"""
SYZ52 — witness LIFT test of the SYZ50 band-realizable interior witnesses.

SYZ50 established: at rate 1/2 the balanced-interior region MEETS the band-realizable
polytope (nonempty), the smallest realizable balanced (4,4,4) config is n=14,k=7,t=2 over
mu14 subset F29, and that config carries 357 genuine constant-syzygy on-domain iota=2
witnesses (three disjoint size-4 pairwise regions S_AC,S_BC,S_AB, a size-4 level set of
R=W_BC/W_AC, 2 leftover points for the triple T).  The open gate SYZ50 relocated to:
the OVER-BUDGET STACK LIFT (does the iota=2 syzygy let a stack beat the pencil accounting?).

This probe RUNS the lift test (SYZ32 methodology) on those witnesses, over the ACTUAL
mu14 subset F29 domain (so the cyclotomic syzygy is realized, not an abstract index set):

 For each witness:
   cores  core_A = S_AB u S_AC u T,  core_B = S_AB u S_BC u T,  core_C = S_AC u S_BC u T
          each size s = 4+4+2 = 10  (rate 1/2, RS[14,7] over mu14 subset F29).
   (1) matroid deficiency d over F29 (and field-independence spot-check);
   (2) build stacks (u0,u1) with all three cores degenerate (null space of the joint
       A_C constraint, exactly SYZ32) -- trace whether the constant syzygy forces the
       local codewords into special position;
   (3) EXACT per-scalar mca-bad count over the FINITE scalars z in F_p, word-level, both
       mcaEvent clauses evaluated on the SAME witness set (ABF26 Def. 4.3 / `mcaEvent`):
       z is bad iff some codeword c agrees with u0 + z*u1 on a set A of size >= s on which
       (u0,u1) is not jointly explained.  Since joint explanation is inherited by subsets,
       it suffices to test each full agreement set A of each close codeword.  (Earlier
       revisions skipped a WHOLE stack whenever some joint threshold set existed anywhere
       and added the direction at infinity to the finite count; both were wrong -- audit
       findings L124 and L123, repository review 2026-10-28.  Closeness of u1 (the point
       at infinity) is now reported separately and never compared to the finite budget.)
   (4) compare max bad-count vs budget n-1 = 13 and pencil ceiling sum(n-s_i) = 12.

Scale check: repeat on the next STRICT-BAND realizable sizes (SYZ50 strict_band_ownership).
The scale enumerator takes a triple region T of exactly the selected size t and allocates
the remaining coordinates explicitly (private coordinates as the profile requires, the rest
unowned), and asserts the actual core / triple / pair-overlap sizes before each lift.  (An
earlier revision assigned EVERY leftover point to T, so at n=16, a=4, t=3 the lifted cores
had size 12 = 3n/4 and pair overlap 8 = k instead of the printed 11 and 7: audit finding
L130.)  The legacy `find_witnesses` keeps that full-leftover convention for importers; it
matches a selected profile only when n - 3a == t, as in the primary n=14 case.

All counts are finite-field sampled lift statistics for these stacks; none is a global
maximum or a refutation of any published theorem or prize instance.
"""
import itertools, random, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached,
    A_C_basis, deficiency)
from probe_syz50_witness_realizability import (band_bounds, balanced_interior,
    strict_band_ownership)

# ---------------------------------------------------------------- roots of unity / witnesses
def _prime_factors(m):
    f=[]; d=2
    while d*d<=m:
        while m%d==0: f.append(d); m//=d
        d+=1
    if m>1: f.append(m)
    return f

def primitive_root_of_unity(p, n):
    assert (p-1)%n==0
    for x in range(2,p):
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in set(_prime_factors(n))):
            return x
    raise RuntimeError("no primitive n-th root")

def _level_set_triples(p, n, a, mu):
    """Yield (AC,BC,AB,leftover,R): disjoint a-subsets S_AC,S_BC of mu_n and a size-a level
    set S_AB of R=W_BC/W_AC on the remaining points; leftover = the other n-3a indices."""
    def Weval(idxset, om):
        r=1
        for i in idxset: r=(r*(om-mu[i]))%p
        return r
    idx=list(range(n))
    for AC in itertools.combinations(idx,a):
        rest1=[i for i in idx if i not in AC]
        for BC in itertools.combinations(rest1,a):
            if BC[0]<AC[0]: continue          # dedupe AC<->BC light symmetry
            rest=[i for i in rest1 if i not in BC]
            level={}; ok=True
            for i in rest:
                d=Weval(AC,mu[i])
                if d%p==0: ok=False; break
                R=(Weval(BC,mu[i])*pow(d,p-2,p))%p
                level.setdefault(R,[]).append(i)
            if not ok: continue
            for R,pts in level.items():
                if len(pts)>=a:
                    for AB in itertools.combinations(pts,a):
                        leftover=tuple(i for i in rest if i not in AB)
                        yield AC, BC, tuple(AB), leftover, R

def find_witnesses(p, n, a, max_wit=None):
    """All (AC,BC,AB,T,R) over mu_n subset F_p: disjoint a-subsets S_AC,S_BC and a size-a
    level set S_AB of R=W_BC/W_AC on the leftover, with T = ALL remaining n-3a points
    (full-leftover convention, kept for importers).  This matches a selected profile with
    triple size t only when n-3a == t; use find_profile_witnesses for any other profile.
    max_wit early-stops enumeration (keeps the larger-n scale check tractable)."""
    g = primitive_root_of_unity(p, n)
    mu = [pow(g,i,p) for i in range(n)]
    wit=[]
    for AC,BC,AB,leftover,R in _level_set_triples(p,n,a,mu):
        wit.append((AC,BC,AB,leftover,R))
        if max_wit is not None and len(wit)>=max_wit:
            return mu, wit
    return mu, wit

def find_profile_witnesses(p, n, a, t, privates=(0,0,0), max_wit=None):
    """Witnesses for the explicit profile ((a,a,a), t, privates) over mu_n subset F_p.

    For each level-set triple (AC,BC,AB) the triple region T ranges over the t-subsets of the
    n-3a leftover points; of the remaining points the first p_A (sorted) are private to core_A,
    the next p_B to core_B, the next p_C to core_C, and the rest are owned by no core.
    Returns (mu, records) with records (AC,BC,AB,T,R,(P_A,P_B,P_C)).
    """
    pA,pB,pC=privates
    if t<0 or min(privates)<0 or 3*a+t+pA+pB+pC>n:
        raise ValueError(f"profile a={a} t={t} privates={privates} does not fit in n={n}")
    g = primitive_root_of_unity(p, n)
    mu = [pow(g,i,p) for i in range(n)]
    recs=[]
    for AC,BC,AB,leftover,R in _level_set_triples(p,n,a,mu):
        for T in itertools.combinations(leftover,t):
            rem=[i for i in leftover if i not in T]
            P=(tuple(rem[:pA]),tuple(rem[pA:pA+pB]),tuple(rem[pA+pB:pA+pB+pC]))
            recs.append((AC,BC,AB,tuple(T),R,P))
            if max_wit is not None and len(recs)>=max_wit:
                return mu, recs
    return mu, recs

# ---------------------------------------------------------------- RS interp over arbitrary alpha
_MATCACHE={}
def build_interp_tensor(alpha, k, s, p):
    """Return (Mall, Tall): Mall[m,j,t]=Lagrange coeff at alpha[j] for node alpha[Tall[m,t]],
    over all k-node sets T drawn from a pigeonhole base so any size-s agreement set meets it in
    >= k points. Vectorized decode: decoded[m,j] = sum_t Mall[m,j,t]*w[Tall[m,t]] (mod p)."""
    key=(tuple(alpha),k,s,p)
    if key in _MATCACHE: return _MATCACHE[key]
    n=len(alpha); base=list(range(min(n, n-(n-s)+2)))
    # completeness guard: every agreement set of size >= s meets the base in >= k points,
    # so every codeword agreeing with a word on >= s points is decoded from some k-subset.
    if s-(n-len(base))<k:
        raise ValueError(f"interpolation base of size {len(base)} is incomplete for "
                         f"n={n}, k={k}, s={s}: need s-(n-|base|) >= k")
    Ts=list(itertools.combinations(base,k)); nm=len(Ts)
    Mall=np.zeros((nm,n,k),dtype=np.int64); Tall=np.array(Ts,dtype=np.int64)
    for m,T in enumerate(Ts):
        for jt,t in enumerate(T):
            den=1
            for t2 in T:
                if t2!=t: den=(den*(alpha[t]-alpha[t2]))%p
            invden=pow(den,p-2,p)
            for j in range(n):
                num=1
                for t2 in T:
                    if t2!=t: num=(num*(alpha[j]-alpha[t2]))%p
                Mall[m,j,jt]=(num*invden)%p
    _MATCACHE[key]=(Mall,Tall,base,n,s,p)
    return _MATCACHE[key]

def _agr_masks(w, tensor):
    """Boolean array (nsel, n): agreement masks of deg<k interpolants agreeing with w on >=s pts."""
    Mall,Tall,base,n,s,p=tensor
    w=np.asarray(w,dtype=np.int64)%p
    wt=w[Tall]                                   # (nm,k)
    dec=np.einsum('mjt,mt->mj', Mall, wt)%p       # (nm,n)
    eq=(dec==w[None,:])                           # (nm,n)
    counts=eq.sum(1)
    sel=counts>=s
    return eq[sel]

def whole_stack_joint_set_exists(u0, u1, tensor):
    """True iff SOME set of >= s points carries a joint explanation of (u0,u1).  This is the
    old SYZ32-style whole-stack filter.  It is NOT an MCA classifier: a joint set in one
    place does not rule out a nonjoint close witness elsewhere (audit finding L124).  Kept
    only as an informational statistic."""
    s=tensor[4]
    A0=_agr_masks(u0,tensor); A1=_agr_masks(u1,tensor)
    if len(A0)==0 or len(A1)==0: return False
    inter=A0.astype(np.int64) @ A1.T.astype(np.int64)   # (a,b) common-point counts
    return bool((inter>=s).any())

def _contained_in_some(A, masks):
    return len(masks)>0 and bool(np.all(masks | ~A[None,:], axis=1).any())

def mca_bad_scalars(u0, u1, tensor):
    """Exact per-scalar MCA classification over the FINITE scalars z in F_p.

    Returns (bad, close): close = z with u0+z*u1 within agreement >= s of the code;
    bad = z for which some close codeword's full agreement set A (|A| >= s) is not jointly
    explained, i.e. NOT (A inside an agreement set of u0 with a codeword AND inside one of u1).
    Exactness: pairJointAgreesOn is inherited by subsets, so a nonjoint witness S exists
    inside A iff A itself is nonjoint; and since |A| >= s >= k, an explaining codeword of u_i
    on A agrees with u_i on >= s points, hence is among the enumerated masks (completeness
    guard in build_interp_tensor).  The point at infinity is not a scalar here."""
    p=tensor[5]; n=tensor[3]
    A0=_agr_masks(u0,tensor); A1=_agr_masks(u1,tensor)
    u0=np.asarray(u0,dtype=np.int64)%p; u1=np.asarray(u1,dtype=np.int64)%p
    bad=[]; close=[]
    for z in range(p):
        masks=_agr_masks((u0+z*u1)%p,tensor)
        if len(masks)==0: continue
        close.append(z)
        for A in masks:
            if not (_contained_in_some(A,A0) and _contained_in_some(A,A1)):
                bad.append(z); break
    return bad, close

def lift_test(alpha, k, s, p, cores, seed=1, trials=4000):
    """SYZ32-style lift test over domain alpha on all-cores-degenerate stacks.

    Returns dict with matroid d, merge stats, maxbad (exact per-scalar finite MCA-bad count,
    comparable to the finite budget), maxbad_raw (finite close scalars, an upper bound for the
    MCA-bad count of that stack), inf_close (stacks whose direction u1 is itself close; the
    point at infinity, reported separately) and whole_stack_joint (stacks the old whole-stack
    filter would have discarded; informational only)."""
    n=len(alpha)
    tensor=build_interp_tensor(alpha,k,s,p)
    def is_close(w): return len(_agr_masks(w,tensor))>0
    def decoded_on(w,C):
        # unique deg<k codeword agreeing with w on all of core C (|C|>=k); None if none
        m=_agr_masks(w,tensor)
        Cs=set(C)
        for row in m:
            agr=set(int(j) for j in np.nonzero(row)[0])
            if Cs<=agr:
                # reconstruct the codeword: interpolate on first k pts of C
                Cl=sorted(C)[:k]
                Mall,Tall,base,nn,ss,pp=tensor
                # brute reconstruct via Lagrange on Cl
                dec=[0]*n
                for j in range(n):
                    acc=0
                    for t in Cl:
                        num=1;den=1
                        for t2 in Cl:
                            if t2!=t:
                                num=(num*(alpha[j]-alpha[t2]))%p
                                den=(den*(alpha[t]-alpha[t2]))%p
                        acc=(acc+w[t]*num*pow(den,p-2,p))%p
                    dec[j]=acc
                return tuple(dec)
        return None

    Db=dual_basis_cached(alpha,k,p)
    AC=[A_C_basis(Db,C,n,p) for C in cores]
    dmat=deficiency(alpha,k,p,cores)[0]

    rng=random.Random(seed)
    maxbad=0; maxbad_raw=0; stacks=0; inf_close=0; whole_stack_joint=0
    merge_tested=0; merge_ok=0; best=None
    for _ in range(trials):
        zs=rng.sample(range(1,p),3)
        rows=[]
        for i in range(3):
            for v in AC[i]:
                rows.append([v[j]%p for j in range(n)]+[(zs[i]*v[j])%p for j in range(n)])
        r,null=rref_rank_nullbasis(rows,2*n,p)
        if not null: continue
        u=[0]*(2*n)
        for b in null:
            c=rng.randrange(p)
            for j in range(2*n): u[j]=(u[j]+c*b[j])%p
        u0,u1=u[:n],u[n:]
        if all(x==0 for x in u1): continue
        # merge check across the three cores
        decs=[decoded_on(u0,cores[i]) for i in range(3)]
        pres=[d for d in decs if d is not None]
        if len(pres)>=2:
            merge_tested+=1
            if all(d==pres[0] for d in pres): merge_ok+=1
        # exact per-scalar classification over finite z; infinity reported separately
        bad,close=mca_bad_scalars(u0,u1,tensor)
        stacks+=1
        if is_close(u1): inf_close+=1
        if whole_stack_joint_set_exists(u0,u1,tensor): whole_stack_joint+=1
        if len(close)>maxbad_raw: maxbad_raw=len(close)
        if len(bad)>maxbad: maxbad=len(bad); best=(zs,bad)
    return dict(d=dmat, maxbad=maxbad, maxbad_raw=maxbad_raw, stacks=stacks,
                inf_close=inf_close, whole_stack_joint=whole_stack_joint,
                merge_tested=merge_tested, merge_ok=merge_ok, best=best)

def cores_of(AC,BC,AB,T,privates=((),(),())):
    """core_A = S_AB u S_AC u T u P_A, core_B = S_AB u S_BC u T u P_B,
    core_C = S_AC u S_BC u T u P_C (privates default to empty)."""
    PA,PB,PC=privates
    core_A=tuple(sorted(set(AB)|set(AC)|set(T)|set(PA)))
    core_B=tuple(sorted(set(AB)|set(BC)|set(T)|set(PB)))
    core_C=tuple(sorted(set(AC)|set(BC)|set(T)|set(PC)))
    return [list(core_A),list(core_B),list(core_C)]

def check_profile(cores, n, k, a, t, privates=(0,0,0)):
    """Assert the ACTUAL lifted geometry matches the selected profile ((a,a,a), t, privates):
    core sizes 2a+t+p_X inside the strict band, pairwise overlaps a+t, triple overlap t.
    Returns the common core size when all cores are equal, else the tuple of sizes."""
    sets=[set(C) for C in cores]
    sizes=tuple(len(C) for C in sets)
    want=tuple(2*a+t+px for px in privates)
    assert sizes==want, f"core sizes {sizes} != profile {want}"
    lo,hi=band_bounds(n)
    assert all(lo<=sz<=hi for sz in sizes), f"core sizes {sizes} outside strict band [{lo},{hi}]"
    for i,j in ((0,1),(0,2),(1,2)):
        ov=len(sets[i]&sets[j])
        assert ov==a+t, f"pair overlap {ov} != a+t = {a+t}"
    tri=len(sets[0]&sets[1]&sets[2])
    assert tri==t, f"triple overlap {tri} != t = {t}"
    return sizes[0] if len(set(sizes))==1 else sizes

# ================================================================ MAIN
if __name__=="__main__":
    print("="*84)
    print("SYZ52: LIFT TEST of the SYZ50 band-realizable interior iota=2 witnesses")
    print("="*84)

    # ---- primary: n=14,k=7,t=2,(4,4,4) over mu14 subset F29 -------------------
    p,n,k,a,t=29,14,7,4,2
    s=a+a+t
    budget=n-1
    ceiling=3*(n-s)
    mu,wit=find_witnesses(p,n,a)
    print(f"\nmu{n} subset F{p}: found {len(wit)} constant-syzygy iota=2 witnesses "
          f"(expected 357).  core size s={s}, budget n-1={budget}, pencil ceiling 3(n-s)={ceiling}")

    # sample for the expensive full lift test (all 357 would be ~357*4000 stacks)
    SAMPLE = int(os.environ.get("SYZ52_SAMPLE","40"))
    rng=random.Random(0)
    sample = wit if len(wit)<=SAMPLE else rng.sample(wit, SAMPLE)
    print(f"lift-testing a representative sample of {len(sample)} witnesses "
          f"(SYZ52_SAMPLE env to change; word-level exact, both mcaEvent clauses)\n")

    agg_maxbad=0; agg_maxraw=0; anomalies=[]; merge_all_ok=True; ds=set()
    zero_bad=0; inf_stacks=0; wsj_stacks=0; all_stacks=0
    assert strict_band_ownership(a,a,a,t,k)==(0,0,0) and n-3*a==t
    for wi,(AC,BC,AB,T,R) in enumerate(sample):
        cores=cores_of(AC,BC,AB,T)
        assert check_profile(cores,n,k,a,t)==s   # full leftover == T here since n-3a == t
        res=lift_test(mu,k,s,p,cores,seed=1+wi,trials=1500)
        inf_stacks+=res['inf_close']; wsj_stacks+=res['whole_stack_joint']
        all_stacks+=res['stacks']
        ds.add(res['d'])
        agg_maxbad=max(agg_maxbad,res['maxbad'])
        agg_maxraw=max(agg_maxraw,res['maxbad_raw'])
        if res['merge_tested'] and res['merge_ok']!=res['merge_tested']:
            merge_all_ok=False
        if res['maxbad']==0: zero_bad+=1
        if res['maxbad']>budget:
            anomalies.append((wi,AC,BC,AB,T,R,res))
        if wi<6:
            print(f"  wit#{wi}: AC={AC} BC={BC} AB={AB} T={T} R={R}")
            print(f"          d={res['d']}  merge {res['merge_ok']}/{res['merge_tested']}  "
                  f"maxbad(exact finite MCA)={res['maxbad']}  max finite close={res['maxbad_raw']}  "
                  f"stacks={res['stacks']} (u1 close/inf: {res['inf_close']}, "
                  f"old whole-stack filter would drop: {res['whole_stack_joint']})")

    print(f"\n  --- aggregate over {len(sample)} witnesses ---")
    print(f"  matroid deficiencies observed d in {sorted(ds)}")
    print(f"  merge (RS-uniqueness) holds on every multi-core stack: {merge_all_ok}")
    print(f"  witnesses with sampled max MCA-bad = 0: {zero_bad}/{len(sample)}")
    print(f"  max exact finite MCA-bad scalars over sampled stacks = {agg_maxbad}   "
          f"(finite budget n-1={budget}, ceiling={ceiling})")
    print(f"  max finite CLOSE scalars over sampled stacks = {agg_maxraw}")
    print(f"  stacks with u1 itself close (infinity; NOT in the finite count): "
          f"{inf_stacks}/{all_stacks}; stacks with some joint threshold set: "
          f"{wsj_stacks}/{all_stacks}")
    if agg_maxbad>budget:
        print(f"  SAMPLED OVER-BUDGET STACKS: {len(anomalies)} witnesses have a sampled stack with "
              f"> {budget} finite MCA-bad scalars (max {agg_maxbad}).")
        print(f"      geometry: pair overlap a+t = {a+t} < k = {k}, so the SYZ32 large-overlap merge")
        print(f"      lemma does not apply to these cores.  This is a finite sampled statistic for")
        print(f"      these stacks, not a global maximum or a refutation of a published bound.")
        for wi,AC,BC,AB,T,R,res in anomalies[:5]:
            print(f"    wit#{wi} AC={AC} BC={BC} AB={AB} T={T} maxbad={res['maxbad']} best={res['best']}")
    else:
        print(f"  n=14: every SAMPLED stack has <= {budget} finite MCA-bad scalars "
              f"(sampled statistic only).")

    # ---- scale check: next strict-band sizes -----------------------------------
    print("\n"+"="*84)
    print("SCALE CHECK: next STRICT-BAND realizable (a,a,a),t configs (SYZ50 ownership check)")
    print("="*84)
    # pick balanced (a,a,a) strict-band configs with a valid root domain mu_n subset F_p
    def small_prime_with_root(n):
        pp=n+1
        while True:
            if (pp-1)%n==0 and all(pp%r for r in range(2,int(pp**.5)+1)) and pp>1:
                return pp
            pp+=1
    # n=18..24 witness enumeration is combinatorially expensive; n=16 already brackets the Johnson
    # edge together with n=14, so the committed scale check stops at n=16 (set SYZ52_SCALE_KMAX
    # higher to push further; witness search is capped by max_wit to stay tractable).
    KMAX=int(os.environ.get("SYZ52_SCALE_KMAX","8"))
    for k in range(8,KMAX+1):
        n=2*k
        # find balanced strict-band (a,a,a),t with explicit private ownership
        found=None
        for a in range(2,k):
            for tt in range(0,k):
                own=strict_band_ownership(a,a,a,tt,k)
                if own is not None and balanced_interior(a,a,a):
                    found=(a,tt,own); break
            if found: break
        if not found:
            print(f"  n={n}: no balanced (a,a,a) strict-band config"); continue
        a,tt,own=found; s2=a+a+tt+own[0]
        assert own[0]==own[1]==own[2]
        pp=small_prime_with_root(n)
        mu2,wit2=find_profile_witnesses(pp,n,a,tt,privates=own,max_wit=30)
        if not wit2:
            print(f"  n={n} k={k} (a,a,a)=({a},{a},{a}) t={tt} s={s2} mu{n}subF{pp}: "
                  f"NO on-domain witness (config strict-band but syzygy-empty)")
            continue
        rng2=random.Random(1)
        samp2=wit2 if len(wit2)<=8 else rng2.sample(wit2,8)
        mx=0; mxr=0; zb=0; nonmerge=0; ds2=set(); infc=0; wsj=0; nst=0
        for wi,(AC,BC,AB,T,R,P) in enumerate(samp2):
            cores=cores_of(AC,BC,AB,T,P)
            assert check_profile(cores,n,k,a,tt,own)==s2
            res=lift_test(mu2,k,s2,pp,cores,seed=1+wi,trials=600)
            mx=max(mx,res['maxbad']); mxr=max(mxr,res['maxbad_raw']); ds2.add(res['d'])
            infc+=res['inf_close']; wsj+=res['whole_stack_joint']; nst+=res['stacks']
            if res['maxbad']==0: zb+=1
            if res['merge_tested']==0: nonmerge+=1
        print(f"  n={n} k={k} (a,a,a)=({a},{a},{a}) t={tt} privates={own} s={s2} (checked) "
              f"overlap a+t={a+tt}(<k? {a+tt<k}) unowned={n-3*a-tt-sum(own)} "
              f"mu{n}subF{pp}: witnesses(capped)={len(wit2)} sampled={len(samp2)} d={sorted(ds2)} "
              f"nonmerge={nonmerge}/{len(samp2)} max exact finite MCA-bad={mx} "
              f"(budget {n-1}, ceiling {3*(n-s2)}, n={n}) max finite close={mxr} "
              f"u1-close stacks={infc}/{nst} joint-set stacks={wsj}/{nst}")
    print("\nDONE.")
