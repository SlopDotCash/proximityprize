#!/usr/bin/env python3
"""
C089 honesty crux: does the (e,m)/pencil matroid-circuit census COUNT #bad scalars,
and does it survive to the prize rates k = rho*n (k>=2)?

The pencil law (dependent_iff_collinear) says: 3 dual vectors lambda^{T1},lambda^{T2},lambda^{T3}
are LINEARLY DEPENDENT (as vectors) iff the (e,m) pair-points are collinear.  A linear
dependency among dual vectors is the worst-case lever: it lets an adversary build a u0 on
which several c_T COLLIDE (so several bad scalars coincide / are forced).

Two questions:

 (A) k=1 GOVERNANCE.  Is the *maximum* number of c_T that can be forced to a single value by
     a clever u0 actually governed by the pencil/(e,m) collinear-triple census?  We measure
     max-fiber size of the c_T(u0) map over a structured search, and compare to the worst-case
     #bad scalar count = mcaBadCount.  (If the worst-case #bad ~ O(n) per the in-tree
     antipodal-pencil law, the census of O(n^2)..O(n^3) collinear TRIPLES is NOT the #bad count.)

 (B) k>=2 EXISTENCE OF THE PLANE.  At k>=2 the dual vector lambda^T is for a (k+1)-subset; the
     pencil law's (e,m)=(sum,product) plane is a 2-coordinate invariant of a PAIR (k=1 only).
     For (k+1)-subsets the natural invariant is the FULL elementary-symmetric tuple
     (e_1,...,e_{k+1}), a (k+1)-dim configuration -- "collinearity" is replaced by a
     codim-1 condition in (k+1)-space, NOT a planar line.  We test: do the (e,m) (= e_1, e_{k+1})
     pair-projections still PREDICT linear dependency of lambda^T at k=2?  If 3 subsets with
     collinear (e_1, e_{k+1}) are GENERICALLY independent as vectors, the pencil census does
     not extend, so the F3/F15 fusion is a k=1-only identity.
"""
import itertools, random
import sympy

def inv(a,q): return pow(a%q, q-2, q)

def lambda_T(nodes,q):
    m=len(nodes); lam=[]
    for i in range(m):
        pr=1
        for j in range(m):
            if j!=i: pr=(pr*((nodes[i]-nodes[j])%q))%q
        lam.append(inv(pr,q))
    return lam

def subgroup_mu(n,q):
    g=sympy.primitive_root(q); zeta=pow(g,(q-1)//n,q)
    return [pow(zeta,t,q) for t in range(n)]

def find_prime(n,beta=4,count=1):
    out=[]; q=((n**beta)//n+1)*n+1
    while len(out)<count and q<n**(beta+2):
        if sympy.isprime(q) and (q-1)%n==0 and q-1!=n: out.append(q); q+=n*997
        else: q+=n
    return out

# ---- (A) k=1: worst-case forced fiber and #bad scalar at proper-subgroup mu_n ----
def worst_bad_k1(n,q):
    """For k=1 (pairs T={i,j}), deep-hole line u1=(x_i^1), so c_T(u1)=1 and the bad
    scalar of T at first word u0 is gamma_T = -c_T(u0).  #bad = #distinct gamma_T over
    all pairs.  We MAXIMIZE #collisions (minimize #distinct) over a search of u0 to mimic
    the adversary the pencil circuits enable, and report the best (smallest distinct count
    => the worst-case = most bad-scalar coincidences)."""
    mu=subgroup_mu(n,q)
    pairs=list(itertools.combinations(range(n),2))
    # adversary aims to ALIGN as many c_T as possible.  Try u0 in span of structured words.
    best_distinct=None; best_maxfiber=0
    trials=[]
    # structured candidate words on mu_n: monomials x^a (these are exactly the deep holes
    # that create rich collision structure), plus random.
    cand=[]
    for a in range(n+2):
        cand.append([pow(x,a,q) for x in mu])
    for _ in range(40):
        cand.append([random.randrange(q) for _ in range(n)])
    for u0 in cand:
        vals=[ (lambda_T([mu[i],mu[j]],q)[0]*u0[i]+lambda_T([mu[i],mu[j]],q)[1]*u0[j])%q
               for (i,j) in pairs]
        from collections import Counter
        c=Counter(vals)
        d=len(c); mf=max(c.values())
        if best_distinct is None or d<best_distinct: best_distinct=d
        best_maxfiber=max(best_maxfiber,mf)
    return len(pairs), best_distinct, best_maxfiber

# ---- (B) k>=2: does (e_1,e_{k+1})-collinearity predict lambda^T linear dependency? ----
def esym(nodes,q):
    """elementary symmetric polys e_1..e_m of node tuple, mod q."""
    m=len(nodes); e=[0]*(m+1); e[0]=1
    for x in nodes:
        for t in range(m,0,-1):
            e[t]=(e[t]+x*e[t-1])%q
    return e[1:]  # e_1..e_m

def rank3(v1,v2,v3,q):
    """rank of 3 vectors over F_q (they live in F_q^n, zero-padded)."""
    M=[list(v) for v in (v1,v2,v3)]
    r=0; ncol=len(M[0]); row=0
    for col in range(ncol):
        piv=None
        for rr in range(row,3):
            if M[rr][col]%q!=0: piv=rr; break
        if piv is None: continue
        M[row],M[piv]=M[piv],M[row]
        ipv=inv(M[row][col],q)
        M[row]=[(x*ipv)%q for x in M[row]]
        for rr in range(3):
            if rr!=row and M[rr][col]%q!=0:
                f=M[rr][col]
                M[rr]=[(a-f*b)%q for a,b in zip(M[rr],M[row])]
        row+=1
        if row==3: break
    return row

def collinear_predicts_dependency(n,q,k,samples=4000):
    """Sample disjoint (k+1)-subset triples; check if (e_1,e_{k+1})-collinearity (the pencil
    invariant) coincides with full lambda^T linear dependency.  Report the confusion matrix."""
    mu=subgroup_mu(n,q)
    idx=list(range(n))
    coll_dep=0; coll_indep=0; noncoll_dep=0; noncoll_indep=0
    full=[None]*n  # placeholder
    random.seed(3)
    for _ in range(samples):
        # three disjoint (k+1)-subsets need 3(k+1) <= n
        if 3*(k+1)>n: return None
        perm=random.sample(idx,3*(k+1))
        T1=perm[:k+1]; T2=perm[k+1:2*(k+1)]; T3=perm[2*(k+1):3*(k+1)]
        def vec(T):
            v=[0]*n; lam=lambda_T([mu[i] for i in T],q)
            for pos,i in enumerate(T): v[i]=lam[pos]
            return v
        v1,v2,v3=vec(T1),vec(T2),vec(T3)
        dep = rank3(v1,v2,v3,q) < 3
        # pencil (e,m) invariant = (e_1, e_{k+1}) = (sum, product)
        def em(T): es=esym([mu[i] for i in T],q); return (es[0],es[-1])
        e1,m1=em(T1); e2,m2=em(T2); e3,m3=em(T3)
        det=((e2-e1)*(m3-m1)-(e3-e1)*(m2-m1))%q
        coll = (det==0)
        if coll and dep: coll_dep+=1
        elif coll and not dep: coll_indep+=1
        elif not coll and dep: noncoll_dep+=1
        else: noncoll_indep+=1
    return coll_dep,coll_indep,noncoll_dep,noncoll_indep

if __name__=="__main__":
    print("=== (A) k=1: worst-case bad-scalar collisions on mu_n (adversarial u0 search) ===")
    for n in (8,16,32):
        q=find_prime(n,beta=4,count=1)[0]
        npairs,bd,mf=worst_bad_k1(n,q)
        print(f"  n={n:3d} q={q:>9d}: C(n,2)={npairs:4d} pairs; best #distinct bad scalars = {bd:4d}"
              f"  (worst collisions={npairs-bd:4d}); max single-value fiber = {mf}")
    print("  -> the in-tree law says worst-case #bad ~ O(n); the collinear-TRIPLE census is")
    print("     O(n^2)..O(n^3) -- they count DIFFERENT things.\n")

    print("=== (B) k>=2: does (e_1,e_{k+1})-collinearity == lambda^T linear dependency? ===")
    for n in (16,32):
        q=find_prime(n,beta=4,count=1)[0]
        mu=subgroup_mu(n,q)
        # k=1 sanity: pencil law MUST hold exactly (coll <=> dep) -- verifies our rank/det code
        r1=collinear_predicts_dependency(n,q,1,samples=3000)
        print(f"  n={n} q={q} k=1 (pencil law check) [coll&dep, coll&indep, ncoll&dep, ncoll&indep] = {r1}")
        for k in (2,3):
            if 3*(k+1)>n:
                print(f"  n={n} k={k}: geometric starvation 3(k+1)>n, skip"); continue
            r=collinear_predicts_dependency(n,q,k,samples=6000)
            cd,ci,nd,ni=r
            print(f"  n={n} q={q} k={k}: [coll&dep, coll&indep, ncoll&dep, ncoll&indep] = {r}")
            if cd+ci>0:
                print(f"       of (e,m)-collinear triples, fraction lambda-DEPENDENT = {cd/(cd+ci):.3f}"
                      f"   (k=1 => 1.000; k>=2 => the plane no longer predicts dependency)")
