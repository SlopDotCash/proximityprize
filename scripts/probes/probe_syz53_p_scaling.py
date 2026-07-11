#!/usr/bin/env python3
"""
SYZ53 -- the DECISIVE p-scaling sweep of the SYZ52 iota=2 interior anomaly.

SYZ52 found: the SYZ50 band-realizable (4,4,4),t=2 interior witnesses over mu14 subset F29
DEFEAT the pencil/merge accounting -- max mca-bad = 19 > pencil ceiling sum(n-s_i)=12 and
budget n-1=13.  The +7 EXCESS was measured only at p=29.  The strip / delta*=1/3 conjecture
survives IFF that excess is a small-field artifact that collapses to the pencil floor at large p
(the G84/G85 first-moment-law prediction).  This probe SETTLES it.

KEY EXACTNESS TOOL (makes the large-p sweep RIGOROUS, not sampled):
  A line word w_z = u0 + z*u1 is s-close  <=>  it has a size-s agreement set S with a deg<k
  codeword.  On any such S (|S|=s>=k) the RS_k|S parity checks H_S (dim s-k) must vanish:
      H_S(u0) + z*H_S(u1) = 0     in  F_p^{s-k}.
  This is AFFINE in z, so each s-subset S carries at MOST ONE candidate z (the vectors
  H_S(u0),H_S(u1) parallel), or all of F (both zero -- flagged).  At n=14, C(14,10)=1001
  subsets; at n=16, C(16,11)=4368 -- both fully enumerable.  Hence for EVERY stack we get the
  EXACT bad-z set at ANY prime p, with no field scan.  (Cross-checked against the SYZ52
  range(p) scan at p=29.)

The witnesses are cyclotomic: the SAME mu_n index subsets are constant-syzygy at every p == 1
(mod n); we recompute the syzygy level-sets at each p and TRACK how many survive as iota=2.

Outputs per p:  #surviving iota=2 witnesses; GLOBAL max mca-bad; the EXCESS = maxbad - ceiling;
pencil-attributable part; distribution; verdict collapse-vs-persist.
"""
import itertools, random, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_syz28_d3_coplanar_crack import (rref_rank_nullbasis, dual_basis_cached,
    A_C_basis, deficiency)
from probe_syz52_witness_lift import (find_witnesses, build_interp_tensor, _agr_masks, cores_of)

# ------------------------------------------------------------------ prime helpers
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def next_prime_1modn(target, n):
    """smallest prime p >= target with p == 1 (mod n)."""
    p = target + ((1 - target) % n)
    if p < target: p += n
    while not is_prime(p): p += n
    return p

# ------------------------------------------------------------------ exact bad-z set (any p)
_PARITY_CACHE={}
def subset_parity(alpha, k, s, p):
    """For every size-s subset S of range(n): the RS_k|S parity checks (dim s-k) as
    numpy arrays.  Returns (subs, Hs) where subs[m] is the index tuple, Hs[m] is a list of
    s-vectors over F_p spanning ker of the k x s Vandermonde on S."""
    n=len(alpha); key=(tuple(alpha),k,s,p)
    if key in _PARITY_CACHE: return _PARITY_CACHE[key]
    subs=list(itertools.combinations(range(n),s)); Hs=[]
    for S in subs:
        V=[[pow(alpha[j],d,p) for j in S] for d in range(k)]   # k x s
        _,null=rref_rank_nullbasis(V, s, p)                    # basis of ker in F^s
        Hs.append([np.array(v,dtype=object) for v in null])
    _PARITY_CACHE[key]=(subs,Hs)
    return subs,Hs

def exact_badz(u0, u1, alpha, k, s, p):
    """EXACT, fully big-int-safe analysis of the pencil {u0 + z u1} at ANY prime p.
    One pass over all size-s subsets S with parity checks H_S (dim s-k):
        a0 = H_S(u0),  a1 = H_S(u1)  in F_p^{s-k}.
      * a0 + z a1 = 0  (a0 parallel a1) -> candidate bad z  (line s-close on S)
      * a1 == 0                          -> u1 itself s-close on S  ('inf' pencil point)
      * a0 == 0 AND a1 == 0              -> COMMON agreement set  => mca-correlated (SYZ32)
                                            AND that subset admits all z (wholefield-on-S)
    Returns (bad_set, inf_close, mca, wholefield)."""
    subs,Hs=subset_parity(alpha,k,s,p)
    u0=[x%p for x in u0]; u1=[x%p for x in u1]
    bad=set(); inf=False; mca=False; wholefield=False
    for S,H in zip(subs,Hs):
        a0=[]; a1=[]
        for h in H:
            s0=0; s1=0
            for idx,j in enumerate(S):
                hj=int(h[idx])
                s0+=hj*u0[j]; s1+=hj*u1[j]
            a0.append(s0%p); a1.append(s1%p)
        a1zero = all(x==0 for x in a1)
        a0zero = all(x==0 for x in a0)
        if a1zero:
            inf=True
            if a0zero: mca=True; wholefield=True
            continue
        c=next(i for i,x in enumerate(a1) if x!=0)
        z=(-a0[c]*pow(a1[c],p-2,p))%p
        if all((a0[i]+z*a1[i])%p==0 for i in range(len(a0))):
            bad.add(z)
    return bad, inf, mca, wholefield

# ------------------------------------------------------------------ lift test (exact, any p)
def _crosscheck(u0,u1,alpha,k,s,p,tensor,bad,inf,wf):
    """Independent validation of exact_badz vs the SYZ52 brute range(p) is_close scan.
    (When wf=True a common-agreement subset makes the whole pencil s-close; that stack is
    mca-filtered so exact_badz reports only the finite parallel-candidate set -- brute is then
    all of F and we only check bad is a subset.)"""
    def is_close(w): return len(_agr_masks(w,tensor))>0
    n=len(alpha)
    brute=set(z for z in range(p) if is_close([(u0[j]+z*u1[j])%p for j in range(n)]))
    if wf:
        assert bad<=brute, f"BADZ SUBSET FAIL p={p}"
    else:
        assert brute==bad, f"BADZ MISMATCH p={p}: exact={sorted(bad)} brute={sorted(brute)}"
        assert is_close(u1)==inf, f"INF MISMATCH p={p}"

def lift_test_exact(alpha, k, s, p, cores, seed=1, trials=1200, verify=False):
    """Fully EXACT, big-int-safe SYZ32 lift test at any prime p."""
    n=len(alpha)
    tensor=build_interp_tensor(alpha,k,s,p) if verify else None
    Db=dual_basis_cached(alpha,k,p)
    AC=[A_C_basis(Db,C,n,p) for C in cores]
    dmat=deficiency(alpha,k,p,cores)[0]
    rng=random.Random(seed)
    maxbad=0; maxraw=0; stacks=0; wholefield=0; dist={}
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
        bad,inf,mca,wf=exact_badz(u0,u1,alpha,k,s,p)
        if verify: _crosscheck(u0,u1,alpha,k,s,p,tensor,bad,inf,wf)
        raw=len(bad)+(1 if inf else 0)
        if wf: wholefield+=1
        maxraw=max(maxraw,raw)
        if mca: continue                              # SYZ32 correlated-agreement filter
        stacks+=1
        if raw>maxbad: maxbad=raw
        dist[raw]=dist.get(raw,0)+1
    return dict(d=dmat, maxbad=maxbad, maxraw=maxraw, stacks=stacks,
                wholefield=wholefield, dist=dist)

# ================================================================ MAIN
def run_config(n,k,a,t, primes, sample_wit=12, trials=1000, verify_at=None, label=""):
    s=a+a+t; budget=n-1; ceiling=3*(n-s)
    print("="*92)
    print(f"CONFIG {label}: n={n} k={k} (a,a,a)=({a},{a},{a}) t={t} s={s}  "
          f"budget n-1={budget}  pencil ceiling 3(n-s)={ceiling}")
    print("="*92)
    rows=[]
    for p in primes:
        mu,wit=find_witnesses(p,n,a)
        nwit=len(wit)
        rng=random.Random(0)
        samp = wit if nwit<=sample_wit else rng.sample(wit,sample_wit)
        gmax=0; gmaxraw=0; ds=set(); wf=0; aggdist={}
        for wi,(AC,BC,AB,T,R) in enumerate(samp):
            cores=cores_of(AC,BC,AB,T)
            vv = (verify_at is not None and p<=verify_at and wi<3)
            res=lift_test_exact(mu,k,s,p,cores,seed=1+wi,trials=trials,verify=vv)
            gmax=max(gmax,res['maxbad']); gmaxraw=max(gmaxraw,res['maxraw'])
            ds.add(res['d']); wf+=res['wholefield']
            for kk,vv2 in res['dist'].items(): aggdist[kk]=aggdist.get(kk,0)+vv2
        excess=gmax-ceiling
        pen_attr=min(gmax,ceiling)
        rows.append((p,nwit,gmax,ceiling,excess))
        top=sorted(aggdist.items())[-6:]
        print(f"  p={p:<12} (log2={np.log2(p):5.2f})  iota2_wit={nwit:<4}  "
              f"max_mca_bad={gmax:<3} raw={gmaxraw:<3}  ceiling={ceiling}  "
              f"EXCESS={excess:+d}  pencil_attr={pen_attr}  d={sorted(ds)}  wf={wf}  "
              f"tail={top}")
    print(f"\n  --- {label} p-law (max_mca_bad, excess vs ceiling {ceiling}) ---")
    for p,nwit,gmax,ceil,exc in rows:
        print(f"    p={p:<13} wit={nwit:<4} maxbad={gmax:<3} excess={exc:+d}")
    return rows

if __name__=="__main__":
    QUICK = os.environ.get("SYZ53_QUICK","0")=="1"
    # ---- primes == 1 (mod 14) at each magnitude ----
    targets14=[29,43,113,197,1009,10007,1000003,1000000007,2**31]
    primes14=[]
    for tgt in targets14:
        p=next_prime_1modn(tgt,14)
        if p not in primes14: primes14.append(p)
    if QUICK: primes14=primes14[:5]
    SKIP14 = os.environ.get("SYZ53_SKIP14","0")=="1"
    print("primes == 1 (mod 14):", primes14)

    if not SKIP14:
        run_config(14,7,4,2, primes14, sample_wit=(6 if QUICK else 12),
                   trials=(400 if QUICK else 1000), verify_at=200, label="MU14")

    # ---- n=16, mu16, primes == 1 (mod 16) ----
    targets16=[17,97,193,1009,10007,1000003]
    if os.environ.get("SYZ53_MU16_LIGHT","0")=="1":
        targets16=[17,97,193,1009,10007]
    primes16=[]
    for tgt in targets16:
        p=next_prime_1modn(tgt,16)
        if p not in primes16: primes16.append(p)
    if QUICK: primes16=primes16[:4]
    print("\nprimes == 1 (mod 16):", primes16)
    run_config(16,8,4,3, primes16, sample_wit=(4 if QUICK else 8),
               trials=(250 if QUICK else 600), verify_at=200, label="MU16")

    # ---- n-scaling at a FIXED large prime: excess growth law in n ----
    # balanced (a,a,a),t realizable interior configs; witness search capped for tractability.
    print("\n"+"="*92)
    print("N-SCALING at fixed large-ish prime (excess growth law in n)")
    print("="*92)
    def small_prime_with_root(nn, target=100003):
        return next_prime_1modn(target, nn)
    nconfigs=[(14,7,4,2),(16,8,4,3),(18,9,5,3),(20,10,5,4),(22,11,6,4),(26,13,7,5)]
    if QUICK: nconfigs=nconfigs[:3]
    for (n,k,a,t) in nconfigs:
        s=a+a+t; ceiling=3*(n-s); budget=n-1
        p=small_prime_with_root(n)
        mu,wit=find_witnesses(p,n,a,max_wit=(8 if QUICK else 20))
        if not wit:
            print(f"  n={n} k={k} (a,a,a)=({a},{a},{a}) t={t} s={s} p={p}: "
                  f"NO on-domain iota=2 witness (config realizable but syzygy-empty)")
            continue
        rng=random.Random(1)
        samp=wit if len(wit)<=6 else rng.sample(wit,6)
        gmax=0; ds=set()
        for wi,(AC,BC,AB,T,R) in enumerate(samp):
            cores=cores_of(AC,BC,AB,T)
            res=lift_test_exact(mu,k,s,p,cores,seed=1+wi,trials=(200 if QUICK else 400))
            gmax=max(gmax,res['maxbad']); ds.add(res['d'])
        print(f"  n={n:<3} k={k} (a,a,a)=({a},{a},{a}) t={t} s={s} p={p:<8} "
              f"wit(capped)={len(wit)} d={sorted(ds)} : max_mca_bad={gmax:<3} "
              f"ceiling={ceiling} budget={budget}  EXCESS={gmax-ceiling:+d}")
    print("\nDONE.")
