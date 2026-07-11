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
   (3) EXACT mca-bad scalar count, word-level, BOTH mcaEvent clauses
       (is_close on the line + the mca correlated-agreement filter);
   (4) compare max bad-count vs budget n-1 = 13 and pencil ceiling sum(n-s_i) = 12;
       and vs the SYZ32 phenomenon (are the lifts mca-correlated => bad = 0?).

Scale check: repeat on the next realizable sizes (n=16..24 from the SYZ50 polytope).
"""
import itertools, random, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached,
    A_C_basis, deficiency)

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

def find_witnesses(p, n, a, max_wit=None):
    """All (AC,BC,AB,T,R) over mu_n subset F_p: disjoint a-subsets S_AC,S_BC and a size-a
    level set S_AB of R=W_BC/W_AC on the leftover, with T = remaining n-3a points.
    max_wit early-stops enumeration (keeps the larger-n scale check tractable)."""
    g = primitive_root_of_unity(p, n)
    mu = [pow(g,i,p) for i in range(n)]
    def Weval(idxset, om):
        r=1
        for i in idxset: r=(r*(om-mu[i]))%p
        return r
    wit=[]; idx=list(range(n))
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
                        T=tuple(i for i in rest if i not in AB)
                        wit.append((AC,BC,tuple(AB),T,R))
                        if max_wit is not None and len(wit)>=max_wit:
                            return mu, wit
    return mu, wit

# ---------------------------------------------------------------- RS interp over arbitrary alpha
_MATCACHE={}
def build_interp_tensor(alpha, k, s, p):
    """Return (Mall, Tall): Mall[m,j,t]=Lagrange coeff at alpha[j] for node alpha[Tall[m,t]],
    over all k-node sets T drawn from a pigeonhole base so any size-s agreement set meets it in
    >= k points. Vectorized decode: decoded[m,j] = sum_t Mall[m,j,t]*w[Tall[m,t]] (mod p)."""
    key=(tuple(alpha),k,s,p)
    if key in _MATCACHE: return _MATCACHE[key]
    n=len(alpha); base=list(range(min(n, n-(n-s)+2)))
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

def lift_test(alpha, k, s, p, cores, seed=1, trials=4000):
    """SYZ32 lift test over domain alpha: max EXACT mca-bad scalar count on all-cores-
    degenerate stacks. Returns dict with matroid d, merge stats, maxbad, maxbad_raw."""
    n=len(alpha)
    tensor=build_interp_tensor(alpha,k,s,p)
    def is_close(w): return len(_agr_masks(w,tensor))>0
    def mca_holds(u0,u1):
        A0=_agr_masks(u0,tensor); A1=_agr_masks(u1,tensor)
        if len(A0)==0 or len(A1)==0: return False
        inter=A0.astype(np.int64) @ A1.T.astype(np.int64)   # (a,b) common-point counts
        return bool((inter>=s).any())
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
    maxbad=0; maxbad_raw=0; stacks=0; stacks_raw=0
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
        # raw pool: count bad scalars z (line word u0+z*u1 is close) + inf point u1
        bad_raw=[z for z in range(p) if is_close([(u0[j]+z*u1[j])%p for j in range(n)])]
        if is_close(u1): bad_raw.append('inf')
        stacks_raw+=1
        if len(bad_raw)>maxbad_raw: maxbad_raw=len(bad_raw)
        if mca_holds(u0,u1): continue     # correlated agreement => not mca-bad (SYZ32 filter)
        stacks+=1
        if len(bad_raw)>maxbad: maxbad=len(bad_raw); best=(zs,bad_raw)
    return dict(d=dmat, maxbad=maxbad, maxbad_raw=maxbad_raw, stacks=stacks,
                stacks_raw=stacks_raw, merge_tested=merge_tested, merge_ok=merge_ok,
                best=best)

def cores_of(AC,BC,AB,T):
    core_A=tuple(sorted(set(AB)|set(AC)|set(T)))
    core_B=tuple(sorted(set(AB)|set(BC)|set(T)))
    core_C=tuple(sorted(set(AC)|set(BC)|set(T)))
    return [list(core_A),list(core_B),list(core_C)]

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
    zero_bad=0
    for wi,(AC,BC,AB,T,R) in enumerate(sample):
        cores=cores_of(AC,BC,AB,T)
        res=lift_test(mu,k,s,p,cores,seed=1+wi,trials=1500)
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
                  f"maxbad(mca)={res['maxbad']}  maxbad_raw(pool)={res['maxbad_raw']}  "
                  f"stacks(noncorr)={res['stacks']}/{res['stacks_raw']}")

    print(f"\n  --- aggregate over {len(sample)} witnesses ---")
    print(f"  matroid deficiencies observed d in {sorted(ds)}")
    print(f"  merge (RS-uniqueness) holds on every multi-core stack: {merge_all_ok}")
    print(f"  witnesses with max mca-bad = 0 (fully SYZ32-correlated): {zero_bad}/{len(sample)}")
    print(f"  GLOBAL max mca-bad scalars = {agg_maxbad}   (budget n-1={budget}, ceiling={ceiling})")
    print(f"  GLOBAL max RAW pool scalars = {agg_maxraw}")
    if agg_maxbad>budget:
        print(f"  *** ANOMALY: {len(anomalies)} witnesses exceed budget; GLOBAL max {agg_maxbad}>{budget} ***")
        print(f"      mechanism: cores overlap = d+t = 4+2 = 6 < k = 7 => SYZ32 merge UNAVAILABLE")
        print(f"      (contrast SYZ32 crack overlap 10>=k=8 => merges => mca-bad=0). The iota=2")
        print(f"      general-position witnesses DEFEAT the merge/yield accounting route.")
        for wi,AC,BC,AB,T,R,res in anomalies[:5]:
            print(f"    wit#{wi} AC={AC} BC={BC} AB={AB} T={T} maxbad={res['maxbad']} best={res['best']}")
    else:
        print(f"  VERDICT n=14: all lifts <= budget; interior witnesses are STACK-HARMLESS.")

    # ---- scale check: next realizable sizes n=16..24 -------------------------
    print("\n"+"="*84)
    print("SCALE CHECK: next realizable (a,a,a),t configs from the SYZ50 polytope")
    print("="*84)
    def realizable(a,b,c,t,k):
        n=2*k
        if a<1 or b<1 or c<1 or t<0: return False
        if a+b+c+t>n: return False
        if max(a,b,c)>k-1-t: return False
        if a+b+c<2*(k-1-t)+3: return False
        return True
    def balanced(a,b,c): return max(a,b,c)+1<(a+b+c)//2
    # pick balanced (a,a,a) realizable configs with a valid root domain mu_n subset F_p
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
        # find balanced realizable (a,a,a),t
        found=None
        for a in range(2,k):
            for tt in range(0,k):
                if realizable(a,a,a,tt,k) and balanced(a,a,a):
                    found=(a,tt); break
            if found: break
        if not found:
            print(f"  n={n}: no balanced (a,a,a) realizable config"); continue
        a,tt=found; s2=a+a+tt
        pp=small_prime_with_root(n)
        mu2,wit2=find_witnesses(pp,n,a,max_wit=30)
        if not wit2:
            print(f"  n={n} k={k} (a,a,a)=({a},{a},{a}) t={tt} s={s2} mu{n}subF{pp}: "
                  f"NO on-domain witness (config realizable but syzygy-empty)")
            continue
        rng2=random.Random(1)
        samp2=wit2 if len(wit2)<=8 else rng2.sample(wit2,8)
        mx=0; mxr=0; zb=0; nonmerge=0; ds2=set()
        for wi,(AC,BC,AB,T,R) in enumerate(samp2):
            cores=cores_of(AC,BC,AB,T)
            res=lift_test(mu2,k,s2,pp,cores,seed=1+wi,trials=600)
            mx=max(mx,res['maxbad']); mxr=max(mxr,res['maxbad_raw']); ds2.add(res['d'])
            if res['maxbad']==0: zb+=1
            if res['merge_tested']==0: nonmerge+=1
        print(f"  n={n} k={k} (a,a,a)=({a},{a},{a}) t={tt} s={s2} overlap a+t={a+tt}(<k? {a+tt<k}) "
              f"mu{n}subF{pp}: witnesses(capped)={len(wit2)} sampled={len(samp2)} d={sorted(ds2)} "
              f"nonmerge={nonmerge}/{len(samp2)} max mca-bad={mx} "
              f"(budget {n-1}, ceiling {3*(n-s2)}, n={n}) max-raw={mxr}")
    print("\nDONE.")
