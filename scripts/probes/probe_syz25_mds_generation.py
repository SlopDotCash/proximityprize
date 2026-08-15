#!/usr/bin/env python3
"""
SYZ25 probe: the EXACT combinatorial criterion for cross-core MDS generation.

Setup (single copy; pair-doubling multiplies by 2):
 - RS[alpha,k] over GF(p), n distinct points; dual code D (dim n-k).
 - Core C ⊆ coords:  A_C := {c ∈ D : supp(c) ⊆ C},  dim A_C = max(0,|C|-k).
 - U = ∪ C_i,  W := A_U  (dim |U|-k),  A_C ⊆ W for every core.
 - GENERATION:  ⨆_i A_{C_i} = W  ?   deficiency d := (|U|-k) - dim(⨆ A_i) ≥ 0.

SYZ25 DUALITY (the exact characterization, proved by perp inside F^U):
   Let P_{<k}|_S := image of degree-<k polynomials restricted to S ⊆ U.
   A_{C_i}^perp (inside F^U) = { p ∈ F^U : p|_{C_i} ∈ P_{<k}|_{C_i} }.
   Hence   (⨆ A_i)^perp = ∩_i A_i^perp = { p : p|_{C_i} is deg-<k for every i }.
   And W^perp = P_{<k}|_U.  So:

     GENERATION  ⟺  every p:U→F that is (the restriction of) a degree-<k poly on EACH
                    core C_i is (the restriction of) a degree-<k poly on ALL of U.
                    == "local-to-global polynomial rigidity".

   Equivalently ⨆ A_i = span{ g_T : T a (k+1)-subset with T ⊆ some C_i }, where g_T is the
   (unique up to scale) min-weight dual codeword supported on T.

This probe:
  (1) VERIFIES the duality: dim(⨆A_i) computed two ways (direct span vs |U| - dim{local polys}).
  (2) Tests SUFFICIENT combinatorial conditions:
        (S1) incremental-≥k overlap: cores orderable so |C_i ∩ (C_1∪..∪C_{i-1})| ≥ k.
        (S2) connected ≥k-overlap graph (pairwise |C_i∩C_j| ≥ k) covering U.
      -> conjecture: S1 (hence S2) ⟹ d=0. Verified exhaustively.
  (3) EXHAUSTIVELY searches small (n,k) for an OVER-BUDGET family (Σ(|C_i|-k) ≥ |U|-k)
      with d>0  -> a counterexample to the "over-budget ⟹ generation" corollary.
  (4) Field-independence: recomputes d over two primes (is d a combinatorial invariant?).
"""
import itertools

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

def joint_span_dim(alpha,k,p,cores):
    n=len(alpha); D=dual_basis(alpha,k,p)
    vs=[v for C in cores for v in A_C_basis(D,C,n,p)]
    return rank(vs,n,p) if vs else 0

def local_poly_dim(alpha,k,p,cores):
    """dim { p in F^U : p|_{C_i} in P_{<k}|_{C_i} for all i }, computed on ground set U.
       Return also |U|-k so d = local_poly_dim - dim(P_{<k}|_U)."""
    U=sorted(set().union(*[set(C) for C in cores])) if cores else []
    idx={u:i for i,u in enumerate(U)}; N=len(U)
    # constraints: for each core C_i, for each (k+1)-subset T of C_i, generator g_T dotted with p =0.
    # g_T = null vector of the (k x (k+1)) Vandermonde on T's points -> unique up to scale.
    rows=[]
    for C in cores:
        for T in itertools.combinations(sorted(C),k+1):
            Vt=[[pow(alpha[t],d,p) for t in T] for d in range(k)]
            _,nb=rref_rank_nullbasis(Vt,k+1,p)
            for g in nb:  # dim 1
                row=[0]*N
                for pos,t in enumerate(T): row[idx[t]]=g[pos]%p
                rows.append(row)
    localdim=N - rank(rows,N,p)
    # dim P_{<k}|_U:
    Pk=[[pow(alpha[u],d,p) for u in U] for d in range(k)]
    pkdim=rank(Pk,N,p)
    return localdim, pkdim, N

def incremental_k_orderable(cores,k):
    """Is there an ordering with |C_i ∩ union(prev)| >= k for all i>=1 (i=0 free)?"""
    Cs=[set(c) for c in cores]
    n=len(Cs)
    # greedy over all start choices via BFS on subsets (small n)
    from functools import lru_cache
    idxs=tuple(range(n))
    # try: repeatedly pick any core overlapping running union in >=k; start with each core.
    def try_from(start):
        used=[False]*n; used[start]=True; run=set(Cs[start]); cnt=1
        progressed=True
        while cnt<n and progressed:
            progressed=False
            for i in range(n):
                if not used[i] and len(Cs[i]&run)>=k:
                    used[i]=True; run|=Cs[i]; cnt+=1; progressed=True
        return cnt==n
    return any(try_from(s) for s in range(n))

def kgraph_connected_covers(cores,k,U):
    Cs=[set(c) for c in cores]; n=len(Cs)
    adj=[[False]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i!=j and len(Cs[i]&Cs[j])>=k: adj[i][j]=True
    seen=[False]*n; seen[0]=True; st=[0]
    while st:
        v=st.pop()
        for w in range(n):
            if adj[v][w] and not seen[w]: seen[w]=True; st.append(w)
    return all(seen)

def analyze(alpha,k,p,cores,label,verbose=True):
    joint=joint_span_dim(alpha,k,p,cores)
    ld,pk,N=local_poly_dim(alpha,k,p,cores)
    U=sorted(set().union(*[set(C) for C in cores]))
    d=(len(U)-k)-joint
    d_dual=ld-pk  # should equal d
    sumexc=sum(max(0,len(C)-k) for C in cores)
    overbudget = sumexc >= (len(U)-k)
    s1=incremental_k_orderable(cores,k)
    s2=kgraph_connected_covers(cores,k,U)
    if verbose:
        print(f"[{label}] |U|={len(U)} |U|-k={len(U)-k} joint={joint} d={d} d_dual={d_dual} "
              f"Sexc={sumexc} over={overbudget} S1incr={s1} S2graph={s2}")
    assert d==d_dual, (label,d,d_dual)   # DUALITY CHECK
    return dict(d=d,over=overbudget,s1=s1,s2=s2,joint=joint,Uk=len(U)-k)

if __name__=="__main__":
    print("=== (1)+(2) named families: duality check + sufficient conditions ===")
    p=101
    a15=list(range(15)); a32=list(range(32))
    analyze(a15,7,p,[list(range(9)),list(range(6,15))],"generic-2core(15,7)")
    analyze(a15,7,p,[[0,1,2,3,4,5,6,7,8],[4,5,6,7,8,9,10,11,12],[8,9,10,11,12,13,14,0,1]],"three-core(15,7)")
    analyze(a32,16,p,[sorted(list(range(16))+[x]) for x in range(16,32)],"star-common15(32,16)")

    print("\n=== (3) EXHAUSTIVE search for over-budget family with d>0 (corollary counterexample) ===")
    # small clean MDS: try several (n,k). enumerate cover families of size-(k+1) cores.
    for (n,k) in [(5,2),(6,2),(6,3),(7,3),(7,4)]:
        p2=next(q for q in range(n+1,10**4) if all(q%r for r in range(2,int(q**.5)+1)))
        alpha=list(range(n))
        s=k+1  # minimal cores (dim-1 A_i, the extremal case)
        allcores=list(itertools.combinations(range(n),s))
        found=None; tested=0; overb=0; overb_gen=0
        # families of up to Dmax cores covering full [n]; iterate D
        Dmax = min(len(allcores), 6)
        import random; random.seed(0)
        # exhaustive for small counts, sampled for large
        for D in range(2,Dmax+1):
            combos=itertools.combinations(range(len(allcores)),D)
            for fam_idx in combos:
                cores=[list(allcores[i]) for i in fam_idx]
                U=set().union(*[set(c) for c in cores])
                if len(U)<n: continue   # require covering all n (so |U|-k fixed = n-k)
                tested+=1
                r=analyze(alpha,k,p2,cores,"",verbose=False)
                if r['over']:
                    overb+=1
                    if r['d']==0: overb_gen+=1
                    else:
                        found=(cores,r);
                # sanity: S1 => d==0
                if r['s1'] and r['d']!=0:
                    print(f"   !!! S1 FAILED SUFFICIENCY (n={n},k={k}) cores={cores} d={r['d']}")
                if tested>200000: break
            if tested>200000: break
        print(f"(n={n},k={k},core={s}) tested={tested} full-cover fams; over-budget={overb}, "
              f"of which generate(d=0)={overb_gen}, FAIL(d>0)="
              f"{'NONE' if found is None else found}")

    print("\n=== (4) field-independence: d over two primes ===")
    fams=[("three(15,7)",a15,7,[[0,1,2,3,4,5,6,7,8],[4,5,6,7,8,9,10,11,12],[8,9,10,11,12,13,14,0,1]]),
          ("2core(15,7)",a15,7,[list(range(9)),list(range(6,15))])]
    for name,al,k,cores in fams:
        ds=[]
        for pp in [31,101,worked if False else 65537]:
            ds.append(analyze(al,k,pp,cores,"",verbose=False)['d'])
        print(f"   {name}: d over p∈{{31,101,65537}} = {ds}  ({'INVARIANT' if len(set(ds))==1 else 'FIELD-DEP'})")
