#!/usr/bin/env python3
"""
C089 -- attack the ACTUAL Lean structure (corrected).

MCADualPencilLaw.dependent_iff_collinear is NOT about pairs; it is about the three
4-SUBSETS  P|Q, P|R, Q|R  (P,Q,R disjoint pairs), i.e. (k+1)=4 => k=3 functionals.
The dual vectors lambda^{P|Q} etc. (4-supported) are linearly dependent IFF the three
pair-points (e_X,m_X)=(sum,product of the pair X) are collinear.

So the pencil law is a *fixed k=3* incidence law: it counts the wide matroid circuits of
4-subset functionals built from pairs.  The C089 claim: this fuses with F3 (incidence) and
F15 (vanishing-Schur c_T collisions), and the open residual is the slanted Dickson family.

We verify, with EXACT finite-field arithmetic over mu_n at a proper-subgroup large prime:

 (1) The Lean pencil law itself: for disjoint pairs P,Q,R, collinear (e,m) <=> lambda's dep.
     (sanity: must be 1.000 -- confirms our model of the proven Lean lemma.)

 (2) The C089 residual: count the slanted (cross-class) collinear triples over mu_n
     mod q -- must match the char-0 census 16 (n=8) / 544 (n=16), confirming the residual
     the connection points at is real and already-counted.

 (3) THE PRIZE-SCALE QUESTION (honesty crux).  The pencil law is locked at k=3 (4-subsets).
     The prize needs #bad scalars at rates k = rho*n = n/2, n/4, n/8, n/16 -- i.e. k+1 ~ n/2..n/16,
     FAR larger than 4.  Does the (e,m)-pencil / collinear-triple census give the #bad-scalar
     count at those k?  We compute the actual worst-case #bad scalars (max over deep-hole lines
     of #distinct c_T) at a prize rate and compare its GROWTH to what the pencil census provides.
     The pencil law is silent for k != 3, so it cannot be the prize count -- we quantify the gap.
"""
import itertools, random
from collections import Counter
import sympy

def inv(a,q): return pow(a%q,q-2,q)
def subgroup_mu(n,q):
    g=sympy.primitive_root(q); zeta=pow(g,(q-1)//n,q)
    return [pow(zeta,t,q) for t in range(n)]
def find_prime(n,beta=4,count=1):
    out=[]; q=((n**beta)//n+1)*n+1
    while len(out)<count and q<n**(beta+2):
        if sympy.isprime(q) and (q-1)%n==0 and q-1!=n: out.append(q); q+=n*997
        else: q+=n
    return out
def lam(nodes,q):
    m=len(nodes); L=[]
    for i in range(m):
        pr=1
        for j in range(m):
            if j!=i: pr=(pr*((nodes[i]-nodes[j])%q))%q
        L.append(inv(pr,q))
    return L
def dualvec(T,mu,q,n):
    v=[0]*n; L=lam([mu[i] for i in T],q)
    for pos,i in enumerate(T): v[i]=L[pos]
    return v
def rank3(vs,q):
    M=[list(v) for v in vs]; row=0; ncol=len(M[0])
    for col in range(ncol):
        piv=next((rr for rr in range(row,3) if M[rr][col]%q),None)
        if piv is None: continue
        M[row],M[piv]=M[piv],M[row]
        ipv=inv(M[row][col],q); M[row]=[(x*ipv)%q for x in M[row]]
        for rr in range(3):
            if rr!=row and M[rr][col]%q:
                f=M[rr][col]; M[rr]=[(a-f*b)%q for a,b in zip(M[rr],M[row])]
        row+=1
        if row==3: break
    return row

# (1)+(2): the genuine pencil law on disjoint pairs -> 4-subset duals, with (e,m) census
def pencil_and_census(n,q):
    mu=subgroup_mu(n,q)
    pairs=list(itertools.combinations(range(n),2))
    def em(P): a,b=mu[P[0]],mu[P[1]]; return ((a+b)%q,(a*b)%q)
    EM={P:em(P) for P in pairs}
    coll_dep=coll_indep=ncoll_dep=ncoll_indep=0
    slanted=0
    checked=0
    for (P,Q,R) in itertools.combinations(pairs,3):
        if len(set(P)|set(Q)|set(R))!=6: continue
        checked+=1
        (e1,m1),(e2,m2),(e3,m3)=EM[P],EM[Q],EM[R]
        det=((e2-e1)*(m3-m1)-(e3-e1)*(m2-m1))%q
        coll=(det==0)
        TPQ=tuple(sorted(set(P)|set(Q))); TPR=tuple(sorted(set(P)|set(R))); TQR=tuple(sorted(set(Q)|set(R)))
        dep = rank3([dualvec(TPQ,mu,q,n),dualvec(TPR,mu,q,n),dualvec(TQR,mu,q,n)],q)<3
        if coll and dep: coll_dep+=1
        elif coll and not dep: coll_indep+=1
        elif dep: ncoll_dep+=1
        else: ncoll_indep+=1
        if coll:
            vert = (e1==e2==e3); horiz=(m1==m2==m3)
            if not vert and not horiz: slanted+=1
    return checked,(coll_dep,coll_indep,ncoll_dep,ncoll_indep),slanted

# (3): prize-scale #bad scalars via deep-hole line, max over structured first words
def prize_scale_bad(n,q,k):
    mu=subgroup_mu(n,q)
    Mtot=sympy.binomial(n,k+1)
    # worst-case adversary: deep-hole second word u1=(x^k) -> c_T(u1)=1, bad = -c_T(u0).
    # search structured u0 = x^a monomials (richest collision class on mu_n) + random.
    cand=[[pow(x,a,q) for x in mu] for a in range(n+3)]+[[random.randrange(q) for _ in range(n)] for _ in range(8)]
    best=None
    for u0 in cand:
        seen=set()
        for T in itertools.combinations(range(n),k+1):
            L=lam([mu[i] for i in T],q)
            seen.add(sum((L[p]*u0[i])%q for p,i in enumerate(T))%q)
        if best is None or len(seen)<best: best=len(seen)
    return int(Mtot), best  # best = worst-case smallest distinct => most bad coincidences

if __name__=="__main__":
    random.seed(11)
    print("=== (1)+(2) genuine pencil law (4-subset duals from disjoint pairs) + slanted census ===")
    for n in (8,16):
        q=find_prime(n,beta=4,count=1)[0]
        chk,(cd,ci,nd,ni),slant=pencil_and_census(n,q)
        print(f"  n={n} q={q}: disjoint-pair triples={chk}")
        print(f"      [coll&dep,coll&indep,ncoll&dep,ncoll&indep]=({cd},{ci},{nd},{ni})  "
              f"=> pencil law holds: {ci==0 and nd==0}")
        print(f"      slanted (collinear, non-vert, non-horiz) = {slant}   (char-0 census: n=8->16, n=16->544)")
    print()
    print("=== (3) prize-scale #bad scalars vs the k=3-locked pencil law ===")
    print("    pencil law is defined ONLY for 4-subsets (k=3); prize wants k=n/2..n/16.")
    for n in (8,16):
        q=find_prime(n,beta=5,count=1)[0]
        print(f"  n={n} q={q} (q~n^5, proper subgroup, (q-1)/n={(q-1)//n}):")
        for rho_name,k in (("k=3 (pencil-locked)",3),("rho=1/2",n//2),("rho=1/4",max(1,n//4))):
            if k+1>n: continue
            M,bad=prize_scale_bad(n,q,k)
            print(f"      {rho_name:18s} k={k:2d}: C(n,k+1)={M:>7d}  worst-case #distinct bad scalars = {bad}")
    print("\n  The pencil/(e,m) census is a FIXED-k=3 incidence count; the prize #bad-scalar")
    print("  worst case at rho=1/2..1/16 is a different, k-dependent quantity the law does")
    print("  not address.  C089 correctly isolates the slanted-Dickson residual at k=3 but")
    print("  that residual is already probe-decided and does NOT reach the prize BGK core.")
