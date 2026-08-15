#!/usr/bin/env python3
"""
SYZ27 probe: local-to-global polynomial gluing in the RATE-1/2 INTERIOR BAND
    2n/3 < s < 3n/4   (equivalently  1/4 < delta < 1/3),  k = n/2.

SYZ26 established:
  * s >= 3n/4  (delta <= 1/4): pairwise overlap 2s-n >= k  =>  RS uniqueness glues
    pairwise  =>  incremental->=k-orderable  =>  generation  =>  d=0  (PROVEN, clean).
  * s = ceil(2n/3) (delta = 1/3 edge): a field-independent d=1 over-budget cover EXISTS.
  * The OPEN interior 1/4 < delta < 1/3 was reported "d=0 for every family tested",
    but the tests were restricted to OVER-BUDGET full covers.

The subtlety SYZ27 resolves.  For D=2 full covers in the band, |U| = 2s - m with
m = |C1 ∩ C2| >= 2s - n.  The deficiency of a 2-core full cover is d = k - m, which is
> 0 throughout the band (m < k).  BUT such a D=2 band cover is UNDER-budget:
    sum_excess = 2(s-k),   |U|-k = 2s-m-k,   over-budget  <=>  m >= k,
which fails in the band.  So deficiency in the band is REAL but confined to sparse
(under-budget) families with too few "bad scalars" to threaten the strip.

THIS PROBE measures the exact coupling  d  vs  D  vs  yield := sum(n - |Ci|)  in the band,
to find the honest generation law:  which (D, yield) regime forces d = 0?

Reuses the exact dual-code linear algebra of probe_syz25/26.
"""
import itertools, random

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

def rank(rows,ncols,p): return rref_rank_nullbasis(rows,ncols,p)[0]

def dual_basis(alpha,k,p):
    n=len(alpha)
    V=[[pow(alpha[i],d,p) for i in range(n)] for d in range(k)]
    return rref_rank_nullbasis(V,n,p)[1]

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

_DC={}
def dual_basis_cached(alpha,k,p):
    key=(tuple(alpha),k,p)
    if key not in _DC: _DC[key]=dual_basis(alpha,k,p)
    return _DC[key]

def joint_span_dim(alpha,k,p,cores):
    n=len(alpha); D=dual_basis_cached(alpha,k,p)
    vs=[v for C in cores for v in A_C_basis(D,C,n,p)]
    return rank(vs,n,p) if vs else 0

def deficiency(alpha,k,p,cores):
    U=sorted(set().union(*[set(C) for C in cores]))
    joint=joint_span_dim(alpha,k,p,cores)
    return (len(U)-k)-joint, len(U), joint

def yield_(cores,n): return sum(n-len(C) for C in cores)
def sum_excess(cores,k): return sum(max(0,len(C)-k) for C in cores)
def min_triple_nonempty(cores):
    """True iff every triple of cores has nonempty common intersection."""
    for a,b,c in itertools.combinations(range(len(cores)),3):
        if not (set(cores[a])&set(cores[b])&set(cores[c])): return False
    return True

def band_sweep(n, trials=60000, seed=0):
    """k=n/2, band 2n/3 < s < 3n/4.  Random full covers, all D.  Tabulate d by (D, over?)."""
    random.seed(seed); k=n//2; alpha=list(range(n)); pts=list(range(n))
    lo = (2*n)//3 + 1                 # s > 2n/3  (strictly interior)
    hi = (3*n)//4 - 1                 # s < 3n/4  (strictly interior)
    if hi < lo: return None
    # cell[(D, over)] -> [count, dpos_count, maxd]
    cell={}
    d0_over=0; dpos_over=0; d0_under=0; dpos_under=0
    yield_dpos=[]; yield_d0_over=[]
    for _ in range(trials):
        D=random.randint(2,6)
        cores=[]; seen=set(); ok=True
        for _c in range(D):
            s=random.randint(lo,hi)
            C=tuple(sorted(random.sample(pts,s)))
            if C in seen: ok=False;break
            seen.add(C); cores.append(list(C))
        if not ok: continue
        U=set().union(*[set(c) for c in cores])
        if len(U)<n: continue   # full cover only
        d,_,_=deficiency(alpha,k,900001 if False else next_prime(n),cores)
        over = sum_excess(cores,k) >= (n-k)
        key=(D,over)
        e=cell.setdefault(key,[0,0,0])
        e[0]+=1
        if d>0: e[1]+=1; e[2]=max(e[2],d)
        if over:
            if d>0: dpos_over+=1; yield_dpos.append(yield_(cores,n))
            else: d0_over+=1; yield_d0_over.append(yield_(cores,n))
        else:
            if d>0: dpos_under+=1
            else: d0_under+=1
    return dict(k=k,lo=lo,hi=hi,cell=cell,
                d0_over=d0_over,dpos_over=dpos_over,
                d0_under=d0_under,dpos_under=dpos_under)

_PC={}
def next_prime(n):
    if n in _PC: return _PC[n]
    q=n+2
    while True:
        if all(q%r for r in range(2,int(q**.5)+1)): break
        q+=1
    _PC[n]=q; return q

def field_indep_check(n, cores, primes=(101,1009,65537,1000003)):
    k=n//2
    return [deficiency(list(range(n)),k,p,cores)[0] for p in primes]

if __name__=="__main__":
    print("="*80)
    print("SYZ27: deficiency d vs (D, budget, yield) in the OPEN interior band 2n/3<s<3n/4")
    print("="*80)
    for n in [16,20,24,28,32]:
        r=band_sweep(n, trials=40000)
        if r is None:
            print(f"\n n={n}: band empty (2n/3..3n/4 has no strict integer)"); continue
        print(f"\n--- n={n}, k={r['k']}, band s in [{r['lo']},{r['hi']}] "
              f"(delta in ({1-r['hi']/n:.3f},{1-r['lo']/n:.3f})) ---")
        print("   OVER-BUDGET   full covers:  d=0 count={:6d}   d>0 count={:6d}".format(
            r['d0_over'], r['dpos_over']))
        print("   UNDER-BUDGET  full covers:  d=0 count={:6d}   d>0 count={:6d}".format(
            r['d0_under'], r['dpos_under']))
        print("   breakdown by (D, over-budget?) -> [tested, d>0 count, max_d]:")
        for key in sorted(r['cell']):
            D,over=key; e=r['cell'][key]
            print(f"      D={D} over={int(over)}: tested={e[0]:6d} dpos={e[1]:5d} maxd={e[2]}")

    print("\n"+"="*80)
    print("Field-independence of the band deficiency (matroid invariant?) on a D=2 witness")
    print("="*80)
    for n in [16,20,24]:
        k=n//2; s=(2*n)//3+1; lo=2*s-n  # minimal pairwise overlap in band
        # explicit D=2 cover: C1={0..s-1}, C2={n-s..n-1}, overlap = 2s-n
        C1=list(range(s)); C2=list(range(n-s,n))
        m=len(set(C1)&set(C2))
        ds=field_indep_check(n,[C1,C2])
        print(f"  n={n} s={s} D=2 overlap m={m} (k={k}): d over p={{101,1009,65537,1000003}} = {ds}"
              f"  predicted k-m={k-m}  over-budget={sum_excess([C1,C2],k)>=n-k}")
