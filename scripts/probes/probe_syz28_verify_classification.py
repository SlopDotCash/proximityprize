#!/usr/bin/env python3
"""
SYZ28 part 2: VERIFY the classification of D=3 band deficiency + word-level lift test.

Hypothesis (from part-1 enumeration): for a D=3 full cover in the band,
    d  =  max(0, (n+k) - min over pairings ( |C_i u C_j| + |C_l| ))
i.e. deficiency is EXACTLY the pair-union subadditivity defect:
    dim(A_1+A_2+A_3) <= (|C_i u C_j| - k) + (|C_l| - k)
because A_i + A_j <= A_{C_i u C_j}.  This upper bound is FIELD-INDEPENDENT by construction
(it is a support/dimension count) -- explaining why every part-1 hit was genuine.

Also: word-level LIFT TEST on the n=16 witness -- construct explicit pencil stacks (u0,u1)
(u0 + z_i*u1 poly on core C_i for chosen z_i) and exhaustively LIST-DECODE every line point
u0+z*u1 over F_p (agreement >= s <=> delta-close).  The lift test reports THREE separate
quantities per sampled stack:
  * CLOSE finite scalars: z in F_p with u0+z*u1 delta-close to RS[n,k].  The fixed n=16
    interpolation window makes this closeness test complete (see `build_interp_mats`).
  * the projective direction z=inf (u1 itself delta-close).  This is a closeness fact only; it
    is NOT a finite scalar and is not compared with the finite-scalar budget.
  * MCA-BAD finite scalars (ArkLib `mcaEvent`): z such that SOME close codeword's agreement set
    S has the pair (u0,u1) NOT jointly explained on S (`not pairJointAgreesOn S`).  Closeness
    alone is not MCA badness: e.g. u0=0, u1=1 makes every line point (and inf) close, yet has
    zero MCA-bad scalars because both rows are global codewords.
Only the MCA-bad count is compared with the yield cap sum(n-s_i) and the budget n.  The close
count is a conservative upper bound on the MCA-bad count of that one fully decoded stack.  All
lift-test numbers are over randomly SAMPLED pencil stacks: they are evidence about those stacks
and do not certify the whole strip.  (Audit 2026-10-28 finding L123; crosslinks T62, L122.)
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, rank, dual_basis_cached,
    A_C_basis, joint_span_dim, deficiency, sum_excess, yield_, band_sizes)

def forced_defect(n,k,cores):
    """(n+k) - min over pairings (|Ci u Cj| + |Cl|), clipped at 0."""
    S=[set(c) for c in cores]
    best=min(len(S[i]|S[j])+len(S[l]) for (i,j,l) in [(0,1,2),(0,2,1),(1,2,0)])
    return max(0,(n+k)-best)

def verify_classification(n, trials=120000, seed=7):
    random.seed(seed); k=n//2; alpha=list(range(n)); pts=list(range(n))
    sizes=band_sizes(n); ceil23=-((-2*n)//3)
    if ceil23 not in sizes: sizes=sizes+[ceil23]
    agree=0; dis_exact=[]; dis_sign=[]
    tested=0
    for _ in range(trials):
        cores=[]; seen=set(); ok=True
        for _c in range(3):
            s=random.choice(sizes)
            C=tuple(sorted(random.sample(pts,s)))
            if C in seen: ok=False;break
            seen.add(C); cores.append(list(C))
        if not ok: continue
        U=set().union(*[set(c) for c in cores])
        if len(U)<n: continue
        tested+=1
        d=deficiency(alpha,k,65537,cores)[0]
        f=forced_defect(n,k,cores)
        if d==f: agree+=1
        else:
            if (d>0)!=(f>0): dis_sign.append((cores,d,f))
            else: dis_exact.append((cores,d,f))
    return tested,agree,dis_exact,dis_sign

# ---------------- word-level lift test (n=16, exact list decoding) ----------------
def build_interp_mats(n,k,s,p):
    """Interpolation matrices: agreement>=s set intersects [0..n-(s- k)-? ] -- use pigeonhole:
    an agreement set of size s=11 in n=16 meets the first 13 positions in >= s-3 = 8 = k points.
    So it suffices to interpolate on 8-subsets of {0..12}.  Precompute, for each such subset T,
    the n x k evaluation matrix M with (M @ w[T])_j = interpolant(alpha_j)."""
    base=list(range(n-(n-s)+2))   # first 13 positions when n=16,s=11
    # Completeness guard: an agreement set of size >= s misses at most n-len(base) window points,
    # so it meets the window in >= s-(n-len(base)) points; that must be >= k for every close
    # codeword to be reproduced by interpolation on some k-subset T of the window.
    if len(base)>n or s-(n-len(base))<k:
        raise ValueError(f"interpolation window {len(base)} is not complete for n={n},k={k},s={s}")
    mats=[]
    for T in itertools.combinations(base,k):
        M=[]
        for j in range(n):
            row=[]
            for t in T:
                num=1;den=1
                for t2 in T:
                    if t2==t: continue
                    num=(num*(j-t2))%p; den=(den*(t-t2))%p
                row.append((num*pow(den,p-2,p))%p)
            M.append(row)
        mats.append((T,M))
    return mats

def best_agreement(w,mats,n,k,s,p):
    for T,M in mats:
        vals=[w[t] for t in T]
        agree=0
        for j in range(n):
            v=0
            row=M[j]
            for a,b in zip(row,vals): v+=a*b
            if v%p==w[j]%p: agree+=1
        if agree>=s: return agree
    return 0

def close_codewords(w,mats,n,k,s,p):
    """COMPLETE list decoding: every DISTINCT codeword c (deg<k on alpha_j=j) agreeing with w on
    >= s positions, as a dict  c (tuple of n values) -> its full agreement set with w (frozenset).
    Completeness: every such c meets the window of `mats` in >= k points (guard in
    `build_interp_mats`), so interpolating w on some k-subset T of its agreement set returns c.
    A subset T already inside a found agreement set can only reproduce that codeword; skip it."""
    out={}
    for T,M in mats:
        if any(A.issuperset(T) for A in out.values()): continue
        vals=[w[t] for t in T]
        dec=tuple(sum(a*b for a,b in zip(M[j],vals))%p for j in range(n))
        agr=frozenset(j for j in range(n) if dec[j]==w[j]%p)
        if len(agr)>=s: out[dec]=agr
    return out

def pair_joint_on(D,u0,u1,k,p):
    """ArkLib `pairJointAgreesOn D`: codewords v0,v1 (deg<k) agree with u0,u1 on all of D.
    For |D| >= k the candidate v_i is the unique interpolant of u_i on any k-subset of D."""
    D=sorted(D)
    if len(D)<k:
        raise ValueError("pair_joint_on is only implemented for |D| >= k")
    T=D[:k]
    def explained(u):
        for j in D:
            v=0
            for t in T:
                num=1;den=1
                for t2 in T:
                    if t2==t: continue
                    num=(num*(j-t2))%p; den=(den*(t-t2))%p
                v=(v+u[t]*num*pow(den,p-2,p))%p
            if v!=u[j]%p: return False
        return True
    return explained(u0) and explained(u1)

def mca_witnesses(u0,u1,z,mats,n,k,s,p):
    """All NONJOINT witness sets of the finite scalar z (ArkLib `mcaEvent`), one per distinct
    close codeword of u0+z*u1: its full agreement set A whenever (u0,u1) is not jointly
    explained on A.  Testing the full agreement set suffices: joint explanation on A implies
    joint explanation on every subset S of A, so a nonjoint S (|S|>=s) inside A forces A
    nonjoint.  z is MCA-bad iff the returned list is nonempty.  Every close codeword is tested;
    one jointly explained close codeword does not rule out another, nonjoint one."""
    w=[(u0[j]+z*u1[j])%p for j in range(n)]
    return [A for A in close_codewords(w,mats,n,k,s,p).values()
            if not pair_joint_on(A,u0,u1,k,p)]

def classify_line(u0,u1,mats,n,k,s,p):
    """Separate (close finite scalars, inf_close, MCA-bad finite scalars) for one stack."""
    close=[]; bad=[]
    for z in range(p):
        w=[(u0[j]+z*u1[j])%p for j in range(n)]
        cw=close_codewords(w,mats,n,k,s,p)
        if not cw: continue
        close.append(z)
        if any(not pair_joint_on(A,u0,u1,k,p) for A in cw.values()): bad.append(z)
    inf_close=bool(close_codewords(u1,mats,n,k,s,p))
    return close,inf_close,bad

def lift_test_n16(witness_cores, p=17, s=11, seed=3, stacks=25):
    """Sampled lift test.  Returns (max MCA-bad finite count, max close finite count, results)
    with results entries (z_i, close finite scalars, inf_close, MCA-bad finite scalars)."""
    n=16;k=8;alpha=list(range(n))
    Db=dual_basis_cached(alpha,k,p)
    random.seed(seed)
    AC=[A_C_basis(Db,C,n,p) for C in witness_cores]
    mats=build_interp_mats(n,k,s,p)
    maxbad=0; maxclose=0; results=[]
    for trial in range(stacks):
        zs=random.sample(range(1,p),3)
        rows=[]
        for i in range(3):
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
        close,inf_close,bad=classify_line(u0,u1,mats,n,k,s,p)
        results.append((zs,close,inf_close,bad))
        maxbad=max(maxbad,len(bad)); maxclose=max(maxclose,len(close))
    return maxbad,maxclose,results

if __name__=="__main__":
    print("="*84)
    print("PART A: exact classification  d == max(0,(n+k) - min_pairings(|Ci u Cj|+|Cl|)) ?")
    print("="*84)
    for n in [16,20,24,28]:
        t,a,de,ds=verify_classification(n, trials=60000 if n<=24 else 30000)
        print(f"  n={n}: tested={t}  exact-agree={a}  value-mismatch={len(de)}  sign-mismatch={len(ds)}", flush=True)
        for cores,d,f in (de+ds)[:5]:
            print(f"     MISMATCH d={d} forced={f} cores={cores}")
    print()
    print("="*84)
    print("PART B: word-level lift test on the n=16 field-independent D=3 witness (p=17)")
    print("   witness cores (pairwise overlaps (6,7,10), triple 6), yield cap = 15 < n = 16")
    print("="*84)
    W=[[1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 15],
       [1, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15],
       [0, 1, 3, 4, 5, 9, 10, 11, 12, 14, 15]]
    mb,mc,res=lift_test_n16(W)
    ninf=sum(1 for r in res if r[2])
    print(f"  sampled stacks tested: {len(res)}")
    print(f"  MAX close finite scalars (closeness only, complete n=16 window): {mc}")
    print(f"  stacks whose direction z=inf is close (projective point, not counted below): {ninf}")
    print(f"  MAX MCA-bad finite scalars (existential nonjoint witness): {mb}")
    for zs,close,inf_close,bad in sorted(res,key=lambda r:(-len(r[3]),-len(r[1])))[:8]:
        print(f"    z_i={zs}: #mca-bad={len(bad)} bad={bad}  #close={len(close)}"
              f"  inf_close={inf_close}")
    print(f"  yield cap sum(n-s_i) = {sum(16-len(C) for C in W)}  |  falsification needs > n = 16"
          " finite MCA-bad scalars")
    print("  VERDICT (sampled stacks only; not a certificate for the whole strip):",
          "no sampled stack exceeds n MCA-bad finite scalars" if mb<=16
          else "OVER-BUDGET SAMPLED STACK (INVESTIGATE)")
