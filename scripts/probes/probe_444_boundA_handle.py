"""
probe_444_boundA_handle.py -- Bound-A: find the EXACT algebraic handle for O_P and test the
sharpest descent hypotheses, with full anti-fabrication calibration.

REFRAMING (eliminant). gamma bad <=> Q_gamma(x) = x^ebar + gamma*x^fbar - P(x) has >= r+1 roots
in mu_n, for some P of deg<r (ebar=e mod n, fbar=f mod n). The r+1 roots are exactly S.
Equivalently: the (r+2)xN 'agreement' linear system has the binomial in the span of monomials
{0..r-1} on S. So bad-ness pins gamma by a (r+1)x(r+1) Vandermonde-with-two-extra-columns minor.

We test, across MANY lines and n in {16,32,64}, which quantity EXACTLY equals O_P, to identify
the Bezout/degree handle. Candidates:
  H_A: O_P = # distinct values of the SCHUR/eliminant resultant Res(T) = prod (T - J). deg = O_P.
  H_B: J determined by an (r-1)-subset of mu_{n/2} via the "square locus": the r+1 roots S, when
       you take products of all C(r+1,2) pairwise products x_i x_j, the n/2-th powers (Legendre)
       give a sign pattern; J <- (set of (r-1) ...). [test square structure of J]
  H_C: the bad gamma satisfy a binomial-coefficient identity making J = (ratio of two
       (r-1)-minors of a Vandermonde on mu_{n/2}).
Concretely we MEASURE:
  - O_P for a representative spread of lines (not just maximizer)
  - whether the multiset of "Legendre signs of the r+1 roots" (#squares among S) is constant per J
  - whether J is determined by the multiset { x_i x_j : i<j } reduced mod squares (mu_{n/2} via x^2)
  - the *fiber field-count*: at fixed (difference-set / squared-multiset), how many distinct J.
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
    raise RuntimeError("no gen")

def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def badset(n,r,e,f,p,w):
    """Return dict J -> list of S (index tuples) for nonzero gamma, plus d,nd."""
    a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    M=max(e-r+1,f-r+1)
    out=defaultdict(list)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g:
            out[pow(g,nd,p)].append(Sidx)
    return out,d,nd

def legendre(a,p): return pow(a,(p-1)//2,p)

def study(n,r,e,f,p):
    w=gen(n,p)
    J2S,d,nd=badset(n,r,e,f,p,w)
    OP=len(J2S)
    half=n//2
    # H_B: #squares among the r+1 roots, constant per J?
    # square in mu_n = even index.
    nsq_per_J=defaultdict(set)        # set of (#even-index roots) per J
    sqmultiset_per_J=defaultdict(set) # squared multiset (mu_{n/2}) per J
    pairprod_per_J=defaultdict(set)   # multiset of pairwise products reduced to mu_{n/2} per J
    for J,Ss in J2S.items():
        for S in Ss:
            neven=sum(1 for i in S if i%2==0)
            nsq_per_J[J].add(neven)
            sqm=tuple(sorted((2*i)%n for i in S))   # x_i^2 has index 2i mod n
            sqmultiset_per_J[J].add(sqm)
            pp=tuple(sorted(((i+j)%n) for a,i in enumerate(S) for j in S[a+1:]))
            pairprod_per_J[J].add(pp)
    nsq_const = all(len(v)==1 for v in nsq_per_J.values())
    sqm_const = all(len(v)==1 for v in sqmultiset_per_J.values())
    pp_const  = all(len(v)==1 for v in pairprod_per_J.values())
    # fiber: group J by squared-multiset; how many J per squared-multiset?
    sqm2J=defaultdict(set)
    for J,Ss in J2S.items():
        for S in Ss:
            sqm=tuple(sorted((2*i)%n for i in S))
            sqm2J[sqm].add(J)
    fibersz=Counter(len(v) for v in sqm2J.values())
    # Legendre of J
    legJ=Counter(legendre(J,p) for J in J2S)
    return dict(OP=OP,d=d,nsq_const=nsq_const,sqm_const=sqm_const,pp_const=pp_const,
                fibersz=dict(sorted(fibersz.items())),legJ=dict(legJ),
                Cnhalf=comb(half,r-1))

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
           5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    p=PRIMES[0]
    print(f"# p={p}")
    for (r,n) in todo:
        e,f=LINES[r](n)
        R=study(n,r,e,f,p)
        print(f"r={r} n={n} line(x^{e},x^{f}) O_P={R['OP']} C(n/2,r-1)={R['Cnhalf']} d={R['d']}")
        print(f"   #squares-among-roots const per J? {R['nsq_const']}")
        print(f"   squared-multiset (mu_n/2) const per J? {R['sqm_const']}")
        print(f"   pairwise-product-multiset const per J? {R['pp_const']}")
        print(f"   fiber sizes (#J per squared-multiset): {R['fibersz']}")
        print(f"   Legendre(J): {R['legJ']}")
