#!/usr/bin/env python3
"""
SYZ28 probe: SETTLE the D=3 over-budget coplanar crack in the rate-1/2 interior band.

SYZ27 found: in the band 2n/3 < s < 3n/4 (k=n/2), over-budget deficiency d>0 is confined to
D=2 (always under-budget) and a RARE D=3 "coplanar shape" with d<=1.  D>=4 over-budget: d=0
in every trial.  This probe ENUMERATES those D=3 hits, tests field-independence (genuine
matroid deficiency vs. small-characteristic accident), classifies the shape, and measures the
yield (bad-scalar count) to decide whether the strip is falsified.

deficiency d = (|U| - k) - dim(joint syndrome span);  |U| = n for a full cover.
The SYZ22 budget is |U| <= n-1.  A genuine (field-independent) over-budget cover whose bad
scalar count exceeds n would falsify the strip.  Reuses probe_syz25/26/27 dual-code algebra.
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

_DC={}
def dual_basis_cached(alpha,k,p):
    key=(tuple(alpha),k,p)
    if key not in _DC: _DC[key]=dual_basis(alpha,k,p)
    return _DC[key]

def A_C_basis(Db,C,n,p):
    Cset=set(C); outside=[j for j in range(n) if j not in Cset]; m=len(Db)
    if not outside: return [d[:] for d in Db]
    rows=[[Db[b][j] for b in range(m)] for j in outside]
    _,combos=rref_rank_nullbasis(rows,m,p)
    out=[]
    for x in combos:
        v=[0]*n
        for b in range(m):
            if x[b]:
                for j in range(n): v[j]=(v[j]+x[b]*Db[b][j])%p
        out.append(v)
    return out

def joint_span_dim(alpha,k,p,cores):
    n=len(alpha); Db=dual_basis_cached(alpha,k,p)
    vs=[v for C in cores for v in A_C_basis(Db,C,n,p)]
    return rank(vs,n,p) if vs else 0

def deficiency(alpha,k,p,cores):
    U=sorted(set().union(*[set(C) for C in cores]))
    joint=joint_span_dim(alpha,k,p,cores)
    return (len(U)-k)-joint, len(U), joint

def sum_excess(cores,k): return sum(max(0,len(C)-k) for C in cores)
def yield_(cores,n): return sum(n-len(C) for C in cores)

def shape_fingerprint(cores):
    """Symmetry-invariant fingerprint: sorted pairwise overlaps + triple intersection size + sizes."""
    D=len(cores); S=[set(c) for c in cores]
    pair=sorted(len(S[a]&S[b]) for a,b in itertools.combinations(range(D),2))
    triple=len(set.intersection(*S)) if D>=3 else None
    sizes=sorted(len(c) for c in cores)
    return (tuple(sizes),tuple(pair),triple)

def next_prime(x):
    q=x+1
    while True:
        if all(q%r for r in range(2,int(q**.5)+1)) and q>1: break
        q+=1
    return q

PRIMES=(101,1009,65537,1000003,2147483647)  # incl huge 2^31-1

def band_sizes(n):
    lo=(2*n)//3+1; hi=(3*n)//4-1
    return list(range(lo,hi+1)) if hi>=lo else []

def enumerate_d3(n, trials=400000, seed=0, include_boundary=True):
    """Random D=3 full covers in the band (+boundary size ceil(2n/3)); record d>0 hits with
    field-independence and shape fingerprint."""
    random.seed(seed); k=n//2; alpha=list(range(n)); pts=list(range(n))
    sizes=band_sizes(n)
    ceil23=-((-2*n)//3)
    if include_boundary and ceil23 not in sizes: sizes=sizes+[ceil23]
    if not sizes: return None
    hits={}          # fingerprint -> dict(count, d_primes_example, over, yield, example_cores, fieldindep)
    total_over=0; total_d0=0; total_dpos=0
    for _ in range(trials):
        cores=[]; seen=set(); ok=True
        for _c in range(3):
            s=random.choice(sizes)
            C=tuple(sorted(random.sample(pts,s)))
            if C in seen: ok=False;break
            seen.add(C); cores.append(list(C))
        if not ok: continue
        U=set().union(*[set(c) for c in cores])
        if len(U)<n: continue                 # full cover only
        over = sum_excess(cores,k) >= (n-k)
        if not over: continue                  # over-budget only (D=3 in band is usually over)
        total_over+=1
        # quick field test on a mid prime first
        d0=deficiency(alpha,k,65537,cores)[0]
        if d0<=0:
            total_d0+=1
            continue
        total_dpos+=1
        ds=[deficiency(alpha,k,p,cores)[0] for p in PRIMES]
        fieldindep=all(x>0 for x in ds)
        fp=shape_fingerprint(cores)
        h=hits.get(fp)
        if h is None:
            hits[fp]=dict(count=1,dvec=ds,over=over,yld=yield_(cores,n),
                          cores=[c[:] for c in cores],fieldindep=fieldindep,
                          maxd=max(ds),alldpos=all(x>0 for x in ds))
        else:
            h['count']+=1
            h['fieldindep']=h['fieldindep'] or fieldindep
            h['maxd']=max(h['maxd'],max(ds))
    return dict(k=k,sizes=sizes,ceil23=ceil23,hits=hits,
                total_over=total_over,total_d0=total_d0,total_dpos=total_dpos)

if __name__=="__main__":
    print("="*84)
    print("SYZ28: enumerate D=3 over-budget deficient covers in the rate-1/2 interior band")
    print("field primes:",PRIMES)
    print("="*84)
    grand_fieldindep=[]
    for n in [16,20,24,28,32]:
        tr = 500000 if n<=24 else 250000
        r=enumerate_d3(n, trials=tr, seed=1)
        if r is None:
            print(f"\n n={n}: band empty"); continue
        print(f"\n--- n={n} k={r['k']} band sizes={r['sizes']} (boundary ceil(2n/3)={r['ceil23']}) ---")
        print(f"   over-budget D=3 full covers sampled: {r['total_over']}   d=0:{r['total_d0']}   d>0:{r['total_dpos']}")
        if not r['hits']:
            print("   NO d>0 D=3 over-budget covers found."); continue
        print(f"   distinct d>0 shape fingerprints: {len(r['hits'])}")
        for fp,h in sorted(r['hits'].items(), key=lambda kv:-kv[1]['count']):
            sizes,pair,triple=fp
            tag="FIELD-INDEP(genuine)" if h['fieldindep'] else "field-accident"
            print(f"     sizes={sizes} pairwise_overlaps={pair} triple_inter={triple} "
                  f"| count={h['count']} d(primes)={h['dvec']} yield={h['yld']} maxd={h['maxd']} [{tag}]")
            if h['fieldindep']:
                grand_fieldindep.append((n,fp,h))
    print("\n"+"="*84)
    print("SUMMARY: field-independent (genuine) D=3 over-budget deficient shapes")
    print("="*84)
    if not grand_fieldindep:
        print("  NONE.  Every D=3 over-budget d>0 hit is a small-characteristic field accident.")
        print("  => the D=3 coplanar crack does NOT carry a genuine matroid deficiency; strip safe at D=3.")
    else:
        for n,fp,h in grand_fieldindep:
            print(f"  n={n} shape={fp} yield={h['yld']} d={h['dvec']} cores={h['cores']}")
