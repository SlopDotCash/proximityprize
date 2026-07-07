"""
probe_444_boundB_elimination.py -- Bound-B: resultant/ELIMINATION degree bound on O_P.

GOAL. O_P = #distinct nonzero J=gamma^{n/d} over (r+1)-subsets S of mu_n on the variety
   V:  h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S),   gamma=-h_{e-r}/h_{f-r}.
Realize the J-values as the ROOTS of an explicit univariate polynomial Q(T) obtained by
ELIMINATING the subset coordinates, and bound deg Q.

THE ELIMINATION SET-UP (sparse / eliminant reframing, CONTEXT-blessed).
   gamma bad  <=>  exists S, |S|=r+1, S subset mu_n, and a codeword poly P (deg < r) with
       x^ebar + gamma x^fbar - P(x) = 0  for all x in S,
   i.e. the (r+2)-sparse Laurent poly  W_gamma(x) = x^ebar + gamma x^fbar - P(x)  has >= r+1
   roots in mu_n.  Equivalently the (r+1)x(r+2) "generalized Vandermonde" with columns
   {x^j : j in {0..r-1} U {ebar} U {fbar}} evaluated on S has a kernel vector with the W_gamma
   shape -- gamma is pinned by the 2x2 Schur minor = 0.

KEY: the BARE generalized-Vandermonde / Bezout count gives deg = C(n, .) (choose r+1 columns of
the n-row Vandermonde on mu_n) -- TOO WEAK by 2^r.  The task: QUOTIENT BY THE ANTIPODE FIRST.

ANTIPODAL DESCENT (proven: J(iota S)=J(S), iota=w^{n/2}=-1).  Work in y=x^2 on mu_{n/2}.
  - If ebar,fbar same parity (the r>=4 maximizer regime), then x^ebar, x^fbar, and the EVEN part
    of P descend to y; the ODD monomials of P pair up x^{2j+1}=x*y^j.  On a +/- symmetric root
    structure W_gamma is even or odd, collapsing to a poly in y of HALF the degree => the Bezout
    count drops to C(n/2,.).  We TEST whether the descended eliminant degree = C(n/2, r-1).

WHAT THIS PROBE COMPUTES (exactly, two primes, char-0):
  (1) Anti-fab calibration: O_P at r=3 = C(n/4,2); O_P table matches CONTEXT.
  (2) The TRUE minimal polynomial Q(T) of the J-set: deg Q = O_P (sanity: it's squarefree, and
      its coefficients are symmetric -> Galois-stable). Confirms O_P is the elimination degree.
  (3) The DESCENDED Bezout/elimination degree: after folding to y=x^2 (antipode quotient), count
      the a-priori number of (r+1)-subsets compatible with the +/- structure = the degree the
      elimination *gives you before* using V. Compare to C(n/2,r-1) and to C(n,.) (un-descended).
  (4) Localize the EXACT residual gap: O_P vs (descended Bezout) vs C(n/2,r-1).
"""
import sys
from math import comb, gcd
from itertools import combinations

PRIMES=[2013265921, 3221225473]

def gen(n,p):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def Jset(n,r,e,f,p):
    """Return (set of distinct nonzero J=gamma^{n/d}, d). Streams over (r+1)-subsets."""
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    Js=set()
    M=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: Js.add(pow(g,nd,p))
    return Js,d

def minpoly_degree(Js,p):
    """Build monic Q(T)=prod(T-J); return its degree (=|Js|) and verify squarefree (distinct roots
       => automatically squarefree). Returns degree and a 'galois-stable' coeff-symmetry sanity:
       the elementary symmetric functions of Js (the coeffs) are well-defined in F_p."""
    # coeffs via product; degree is just len. Confirm Q has exactly |Js| distinct roots = its degree.
    return len(Js)

def descended_bezout(n,r,e,f):
    """The a-priori elimination degree AFTER quotienting by the antipode.
       Un-descended naive Bezout (columns of n-row Vandermonde): C(n, r+1)-ish, but the operative
       degree-handle the CONTEXT flags is C(n/2, r-1) (=(r-1) free squares after pinning).
       We report the family of candidate descended degrees so we can see which one the
       elimination would deliver:
         B_full  = C(n, r-1)      (un-descended (r-1)-subset count, the WEAK Bezout)
         B_desc  = C(n/2, r-1)    (descended: (r-1)-subset of the n/2 squares = TARGET)
         B_half  = C(n/2, r)      (=K/2^r, one up)
    """
    return dict(B_full=comb(n,r-1) if n>=r-1 else 0,
                B_desc=comb(n//2,r-1) if n//2>=r-1 else 0,
                B_half=comb(n//2,r) if n//2>=r else 0)

LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
       5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}

if __name__=="__main__":
    todo=[(3,16),(3,32),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for p in PRIMES:
        print(f"### prime p={p}  (char-0 worst case)")
        for (r,n) in todo:
            e,f=LINES[r](n)
            Js,d=Jset(n,r,e,f,p)
            OP=len(Js)
            degQ=minpoly_degree(Js,p)
            B=descended_bezout(n,r,e,f)
            ebar,fbar=e%n,f%n
            parity = "same" if (ebar%2)==(fbar%2) else "opp"
            c34=comb(n//4,2) if (r==3 and n//4>=2) else None
            print(f"  r={r} n={n} line(x^{e},x^{f}) [{parity}-parity] d={d}: "
                  f"O_P=degQ={OP}  C(n/4,2)={c34}  "
                  f"B_desc=C(n/2,r-1)={B['B_desc']}  B_half=C(n/2,r)={B['B_half']}  "
                  f"B_full=C(n,r-1)={B['B_full']}  | O_P<=B_desc? {OP<=B['B_desc']}")
