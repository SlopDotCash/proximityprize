"""
probe_444_boundA_eliminant_degree.py -- Bound-A via ELIMINANT DEGREE (the live route M2 flagged).

Idea: the bad-gamma values J=gamma^{n/d} are the roots of a SINGLE univariate polynomial R(T)
obtained by eliminating S from the system. We construct R(T) honestly and measure deg R, then
see whether deg R (or its squarefree part) <= C(n/2, r-1), and WHY.

Construction of the eliminant we can actually build:
  For a FIXED gamma, "gamma is bad" means: exists (r+1)-subset S of mu_n with
     x^ebar + gamma x^fbar  agreeing with a deg<r poly on S
  <=> the (r+1) points (x, x^ebar+gamma x^fbar) lie on a deg<r poly
  <=> the divided difference / (r+1)-st finite difference of the function
        F_gamma(x) = x^ebar + gamma x^fbar   over the (r+1) nodes S  VANISHES.
  The (r+1)-node divided difference of F is
     DD_S(F_gamma) = sum_{x in S} F_gamma(x) / prod_{y in S, y!=x} (x - y).
  S bad  <=>  DD_S(F_gamma)=0  <=>  gamma = - DD_S(x^ebar) / DD_S(x^fbar).
  So gamma(S) = - D_e(S)/D_f(S) where D_m(S) = DD_S(x^m) is a Schur poly s_{(m-r,0..)}(S) up to
  sign (the (r+1)-node divided difference of x^m is the complete-homog h_{m-r}(S)). This matches
  the h-ratio EXACTLY (gamma=-h_{ebar-r}/h_{fbar-r}); good cross-check.

Now to ELIMINATE S: the set of attainable gamma over all S is the IMAGE of the rational map
  S |-> -h_{ebar-r}(S)/h_{fbar-r}(S),  S ranging over (r+1)-subsets.
This is a finite set; its size is #distinct gamma; O_P = #distinct gamma^{n/d}.

We measure the GENERATING polynomial degree two ways:
 (A) R_full(T) = prod_{distinct gamma} (T-gamma); deg = #distinct gamma = (n/d)*O_P  [orbit-blown]
 (B) R_orb(T)  = prod_{distinct J} (T-J);          deg = O_P                         [the target]
and we test the HYPOTHESIS that R_orb is the squarefree part of a resultant of TWO symmetric
functions on mu_{n/2}, whose Bezout degree is C(n/2,r-1).

CRUCIAL NEW TEST (the actual mechanism candidate, "Wronskian/Schur on mu_{n/2}"):
  Same-parity lines collapse F_gamma onto EVEN powers => substitute u=x^2, u ranges over mu_{n/2}.
  Then F_gamma(x)=x^c (x^{ebar-c}... ) -- factor out the common parity. For e,f BOTH even,
  x^ebar=u^{ebar/2}, x^fbar=u^{fbar/2}, P(x) even-part lives on u in mu_{n/2}. The (r+1)-node
  condition on mu_n folds to a condition on the SQUARES u, and the agreement degree halves only
  if S is antipodally symmetric (the M1 blocker). We instead test the ODD-part separately:
  decompose by parity of indices and measure the bipartite (squares x nonsquares) structure of S.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
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

def gammas(n,r,e,f,p,w):
    a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    M=max(e-r+1,f-r+1)
    gset=set(); J2g=defaultdict(set)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g:
            gset.add(g); J2g[pow(g,nd,p)].add(g)
    return gset,J2g,d,nd

def study(n,r,e,f,p):
    w=gen(n,p)
    gset,J2g,d,nd=gammas(n,r,e,f,p,w)
    ndg=len(gset)               # #distinct gamma  = (n/d)*O_P
    OP=len(J2g)
    # check each J really has exactly n/d preimages (full orbit) -- prior claim
    orbsz=Counter(len(v) for v in J2g.values())
    return dict(ndg=ndg,OP=OP,d=d,nd=nd,orbsz=dict(orbsz),Cnh=comb(n//2,r-1),
                ratio=OP/comb(n//2,r-1) if comb(n//2,r-1) else 0)

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
           5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32),(4,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    p=PRIMES[0]
    print(f"# p={p}  -- #distinct gamma vs O_P vs orbit structure")
    for (r,n) in todo:
        e,f=LINES[r](n)
        R=study(n,r,e,f,p)
        print(f"r={r} n={n} line(x^{e},x^{f}) d={R['d']} nd={R['nd']}: "
              f"#gamma={R['ndg']} O_P={R['OP']} (=#gamma/nd? {R['ndg']==R['OP']*R['nd']}) "
              f"orbsz={R['orbsz']} C(n/2,r-1)={R['Cnh']} ratio={R['ratio']:.3f}")
