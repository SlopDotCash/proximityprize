#!/usr/bin/env python3
"""
SYZ26 probe: does SYZ25's rigidity-deficient cover LIFT to an over-budget bad-scalar
stack inside the RATE-1/2 STRIP?

THE DECISIVE QUESTION.  SYZ25 exhibited a rigidity-deficient (d>0) over-budget cover
    n=6, k=3, C = {{0,1,4,5},{0,2,3,5},{1,2,3,4}}  (d=1)
but its cores have size k+1 = 4 (MINIMAL cores).  SYZ24's "d=0 for every over-budget
family" verdict was ALSO measured only on minimal (size-(k+1)) star/nested cores.

The STRIP is different.  A bad scalar's witness/core S is an AGREEMENT set: for radius
delta in the strip (Johnson ~ 0.293, 1/3) at rate 1/2, |S| = t >= (1-delta) n, so strip
cores have size  s >= t-1 ~ 2n/3  (NOT k+1 = n/2+1).  Two strip cores overlap
    |Ci ∩ Cj| >= 2s - n >= 2(2n/3) - n = n/3,
which is < k = n/2, so the SYZ25 sufficient condition (incremental->=k overlap, S1) is
NOT automatically forced.  Hence d>0 might survive.  THIS PROBE DECIDES.

Steps:
 (1) EXISTENCE.  For k=n/2, sweep the core-size lower bound s_min from k+1 up to n-1.
     Exhaustively / randomly search full covers by size->=s_min cores that are OVER-BUDGET
     (sum(|Ci|-k) >= |U|-k) and DISTINCT-support, and report the max deficiency d found at
     each s_min.  Question: does d>0 ever occur once s_min >= ceil(2n/3) (strip regime)?
 (2) If YES: attempt the FULL LIFT (find a non-codeword stack realizing the cover with
     over-budget bad scalars).  If NO: that non-existence IS the theorem; certify the
     mechanism (large cores force incremental->=k overlap => S1 => d=0).
 (3) Field-independence of d (matroid invariant), primes {31,101,65537}.

Uses the exact dual-code linear algebra of probe_syz25_mds_generation.py.
"""
import itertools, random

# ---------- linear algebra over GF(p) (verbatim style from probe_syz25) ----------
def rref_rank_nullbasis(rows, ncols, p):
    M=[r[:] for r in rows]; r=0; piv=[]
    for c in range(ncols):
        s=None
        for i in range(r,len(M)):
            if M[i][c]%p!=0: s=i;break
        if s is None: continue
        M[r],M[s]=M[s],M[r]
        iv=pow(M[r][c],p-2,p); M[r]=[(x*iv)%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%p!=0:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(ncols)]
        piv.append(c); r+=1
        if r==len(M): break
    Rr=M[:r]; free=[c for c in range(ncols) if c not in piv]
    basis=[]
    for fc in free:
        v=[0]*ncols; v[fc]=1
        for ri,pc in enumerate(piv): v[pc]=(-Rr[ri][fc])%p
        basis.append(v)
    return r, basis

def rank(rows,ncols,p):
    return rref_rank_nullbasis(rows,ncols,p)[0]

def dual_basis(alpha,k,p):
    n=len(alpha)
    V=[[pow(alpha[i],d,p) for i in range(n)] for d in range(k)]
    return rref_rank_nullbasis(V,n,p)[1]  # null space of Vandermonde, dim n-k

def A_C_basis(D,C,n,p):
    Cset=set(C); outside=[j for j in range(n) if j not in Cset]; m=len(D)
    if not outside: return [d[:] for d in D]
    rows=[[D[b][j] for b in range(m)] for j in outside]
    _,combos=rref_rank_nullbasis(rows,m,p)
    out=[]
    for x in combos:
        v=[0]*n
        for b in range(m):
            if x[b]:
                for j in range(n): v[j]=(v[j]+x[b]*D[b][j])%p
        out.append(v)
    return out

_DUALCACHE={}
def dual_basis_cached(alpha,k,p):
    key=(tuple(alpha),k,p)
    if key not in _DUALCACHE: _DUALCACHE[key]=dual_basis(alpha,k,p)
    return _DUALCACHE[key]

def joint_span_dim(alpha,k,p,cores):
    n=len(alpha); D=dual_basis_cached(alpha,k,p)
    vs=[v for C in cores for v in A_C_basis(D,C,n,p)]
    return rank(vs,n,p) if vs else 0

def deficiency(alpha,k,p,cores):
    U=sorted(set().union(*[set(C) for C in cores]))
    joint=joint_span_dim(alpha,k,p,cores)
    return (len(U)-k)-joint, len(U), joint

def incremental_k_orderable(cores,k):
    Cs=[set(c) for c in cores]; n=len(Cs)
    def try_from(start):
        used=[False]*n; used[start]=True; run=set(Cs[start]); cnt=1; prog=True
        while cnt<n and prog:
            prog=False
            for i in range(n):
                if not used[i] and len(Cs[i]&run)>=k:
                    used[i]=True; run|=Cs[i]; cnt+=1; prog=True
        return cnt==n
    return any(try_from(s) for s in range(n))

def sum_excess(cores,k):
    return sum(max(0,len(C)-k) for C in cores)

# ---------- (1) EXISTENCE sweep ----------
def sweep_existence(n, k, p, s_range, trials=40000, D_range=(3,6), seed=0):
    """Random search for OVER-BUDGET, distinct-support full covers with cores of size >= s_min,
       tracking the maximum deficiency d found. Returns {s_min: (maxd, example)}."""
    random.seed(seed)
    alpha=list(range(n))
    pts=list(range(n))
    out={}
    for s_min in s_range:
        maxd=0; ex=None; n_over=0; n_over_pos=0; tested=0
        # deterministic seed families + random
        for _ in range(trials):
            D=random.randint(*D_range)
            cores=[]
            seen=set()
            ok=True
            for _c in range(D):
                s=random.randint(s_min, n)  # size in [s_min, n]
                C=tuple(sorted(random.sample(pts, s)))
                if C in seen:   # distinct supports required
                    ok=False; break
                seen.add(C); cores.append(list(C))
            if not ok: continue
            U=set().union(*[set(c) for c in cores])
            if len(U)<n: continue          # require covering all n so |U|-k = n-k fixed
            if sum_excess(cores,k) < (len(U)-k): continue  # over-budget only
            tested+=1; n_over+=1
            d,_,_=deficiency(alpha,k,p,cores)
            if d>0:
                n_over_pos+=1
                if d>maxd:
                    maxd=d; ex=[c[:] for c in cores]
        out[s_min]=dict(maxd=maxd, example=ex, tested=tested,
                        n_over=n_over, n_over_pos=n_over_pos)
    return out

# ---------- (1b) targeted lift of SYZ25 shape to strip sizes ----------
def scale_syz25_shape(n, k, p):
    """The SYZ25 shape at n=6,k=3 was 3 cores, each the complement of a distinct 2-subset's
       'opposite' pattern.  Generalize: 3 cores, each missing a disjoint block, sizes ~2n/3.
       Try to realize a strip-sized version and measure d."""
    alpha=list(range(n))
    res=[]
    # 3-core symmetric families with small pairwise overlaps but each large.
    third=n//3
    # cores = complements of the 3 disjoint thirds -> each size 2n/3, pairwise overlap n/3.
    blocks=[list(range(0,third)), list(range(third,2*third)), list(range(2*third,n))]
    cores=[sorted(set(range(n))-set(b)) for b in blocks]
    d,U,joint=deficiency(alpha,k,p,cores)
    res.append(("complement-of-thirds", cores, [len(c) for c in cores], d,
                sum_excess(cores,k), U-k if isinstance(U,int) else len(range(U))))
    return res, cores

if __name__=="__main__":
    print("="*78)
    print("SYZ26: does a rigidity-deficient cover survive at STRIP core sizes (>= ~2n/3)?")
    print("="*78)

    for n in [12, 18, 24]:
        k=n//2
        p=next(q for q in range(n+2,10**5) if all(q%r for r in range(2,int(q**.5)+1)))
        strip_smin=-(-2*n//3)  # ceil(2n/3)
        s_range=list(range(k+1, n))   # from minimal (k+1) up to n-1
        print(f"\n--- n={n}, k={k}, p={p}, strip core-size threshold ceil(2n/3)={strip_smin} ---")
        res=sweep_existence(n,k,p,s_range,trials=8000)
        for s_min in s_range:
            r=res[s_min]
            tag=" <-- STRIP" if s_min>=strip_smin else ""
            print(f"  s_min={s_min:2d}: over-budget distinct covers tested={r['n_over']:6d}  "
                  f"with d>0={r['n_over_pos']:5d}  max_d={r['maxd']}{tag}")
            if r['maxd']>0 and s_min>=strip_smin and r['example']:
                print(f"        STRIP-SIZED d>0 EXAMPLE: {r['example']}")

        # targeted symmetric shape
        shape,_=scale_syz25_shape(n,k,p)
        for name,cores,sizes,d,sexc,_ in shape:
            over = sexc >= (len(set().union(*[set(c) for c in cores]))-k)
            print(f"  [shape {name}] sizes={sizes} d={d} sum_excess={sexc} over-budget={over} "
                  f"S1incr={incremental_k_orderable(cores,k)}")

    print("\n"+"="*78)
    print("(3) field-independence of d for the complement-of-thirds strip shape")
    print("="*78)
    for n in [18,24,30]:
        k=n//2
        ds=[]
        for pp in [31,101,65537]:
            shape,cores=scale_syz25_shape(n,k,pp)
            ds.append(shape[0][3])
        inv = "INVARIANT" if len(set(ds))==1 else "FIELD-DEP"
        print(f"  n={n}: d over p in {{31,101,65537}} = {ds}  ({inv})")

    print("\n"+"="*78)
    print("(4) DECISIVE: critical core-size threshold for FIELD-INDEPENDENT deficiency.")
    print("    A d>0 cover 'lifts' only if its deficiency is a genuine matroid invariant")
    print("    (survives over the huge prize field), NOT a small-characteristic accident.")
    print("    Claim: field-indep d>0 needs core size <= ceil(2n/3) (delta >= 1/3), i.e. the")
    print("    strip's EXCLUDED top edge; the OPEN strip interior (delta<1/3, core>2n/3) is")
    print("    deficiency-free => generation forced => strip budget safe.  STRIP TRUE-mechanism.")
    print("="*78)
    LARGE=[101,1009,65537,1000003]
    def field_indep_dpos(n,k,cores,seedp):
        if deficiency(list(range(n)),k,seedp,cores)[0]==0: return False
        return all(deficiency(list(range(n)),k,pp,cores)[0]>0 for pp in LARGE)
    for n in [12,16,20,24]:
        k=n//2
        seedp=next(q for q in range(n+2,10**4) if all(q%r for r in range(2,int(q**.5)+1)))
        edge=-(-2*n//3)  # ceil(2n/3) = delta=1/3 strip edge
        random.seed(0); pts=list(range(n)); best=-1; ex=None
        for _ in range(15000):
            D=random.randint(3,5); s0=random.randint(k+1,n-1)
            cores=[]; seen=set(); ok=True
            for _c in range(D):
                sz=random.randint(s0,n); C=tuple(sorted(random.sample(pts,sz)))
                if C in seen: ok=False;break
                seen.add(C); cores.append(list(C))
            if not ok: continue
            U=set().union(*[set(c) for c in cores])
            if len(U)<n or sum_excess(cores,k)<len(U)-k: continue
            ms=min(len(c) for c in cores)
            if ms>best and field_indep_dpos(n,k,cores,seedp):
                best=ms; ex=[c[:] for c in cores]
        delta = 1-best/n if best>0 else float('nan')
        print(f"  n={n} k={k}: max field-INDEP deficient min-core-size s*={best}  "
              f"ceil(2n/3)={edge}  delta@s*={delta:.3f}  "
              f"({'s*<=edge, delta>=1/3 -> deficiency OUTSIDE open strip  [OK]' if best<=edge else 'EXCEEDS EDGE'})")
        if ex: print(f"      witness: {ex}")
