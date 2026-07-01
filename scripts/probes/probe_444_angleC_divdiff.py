"""
probe_444_angleC_divdiff.py -- recast gamma via DIVIDED DIFFERENCES and study the value count.

FACT (to verify): for an (r+1)-node set S, the leading (deg-r) coeff of the interpolant of
values {v_i} is the divided difference  v[S] = sum_i v_i / prod_{j!=i}(x_i - x_j).
For v_i = x_i^m this equals the complete-homogeneous symmetric poly h_{m-r}(x_S).
S bad <=>  (x^e)[S] + gamma*(x^f)[S] = 0  <=> gamma = -h_{e-r}(S)/h_{f-r}(S).

So gamma = -h_{e-r}(S)/h_{f-r}(S). Now the KEY for Angle C:
  Both h_{e-r}, h_{f-r} are SYMMETRIC in the nodes x_i=g^i.
  gamma^{n/d} (d=gcd(e-f,n)) is dilation-INVARIANT.

We test the SHARPEST possible Angle-C handle:
  CLAIM: O_P = #distinct gamma <= #distinct values of (h_{e-r}(S) : h_{f-r}(S)) in P^1.
  And the map S -> [h_{e-r}:h_{f-r}] is a SYMMETRIC, dilation-equivariant rational map.
  After quotient by dilation, it lands in a weighted P^1; the # of distinct image points
  is what we want.

CONCRETE degree handle to TEST:  the image set {gamma} is contained in the ZERO SET of a single
univariate polynomial Res(T) = Resultant_S( h_{e-r}(S) + (1/T) h_{f-r}(S)*... ) -- i.e. the
values gamma are roots of an explicit polynomial whose degree bounds O_P.

Simplest version we CAN compute: for fixed line, collect the set G={gamma}. Find the minimal
degree monic polynomial over F_p vanishing on G^{n/d} (the coset reps). Its degree = O_P
(tautology). The QUESTION is whether O_P has a clean a-priori (combinatorial) upper bound.

Here we test a specific structural conjecture for the MONOMIAL line:
  Write S as a subset of Z/n. gamma=-h_{e-r}/h_{f-r}. Conjecture: gamma is a function ONLY of
  the "dilation orbit type" of S AND a bounded set of discrete choices.
We measure: #distinct gamma vs combinatorial counts C(n/2,r), C(n/4,*), 2^r etc, to find the
governing crude formula.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

# verify divided-difference == h_{m-r}
def divdiff(xs,vs,p=P):
    s=0
    k=len(xs)
    for i in range(k):
        den=1
        for j in range(k):
            if j!=i: den=den*((xs[i]-xs[j])%p)%p
        s=(s+vs[i]*pow(den,p-2,p))%p
    return s

def verify_dd(n,r):
    w=gen(n); a0=r+1
    for Sidx in list(combinations(range(n),a0))[:30]:
        xs=[pow(w,i,P) for i in Sidx]
        H=hpow(xs,max(0,n),P)
        for m in [r,r+1,r+2]:
            vs=[pow(x,m,P) for x in xs]
            dd=divdiff(xs,vs)
            assert dd==H[m-r], (n,r,m,Sidx)
    return True

def badgamma(Sidx,w,e,f,r,p=P):
    xs=[pow(w,i,p) for i in Sidx]
    M=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return None
    H=hpow(xs,M,p)
    her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
    if (her*hfr1-hfr*her1)%p!=0: return None
    if hfr==0: return ('zero' if her==0 else 'inf',)
    g=(-her*pow(hfr,p-2,p))%p
    return ('val',g) if g!=0 else ('zero',)

def OP_of(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    nz=set()
    for Sidx in combinations(range(n),a0):
        res=badgamma(Sidx,w,e,f,r,p)
        if res and res[0]=='val': nz.add(res[1])
    cosets=set(pow(g,nd,p) for g in nz)
    return len(cosets), nz

if __name__=="__main__":
    print("verify divided-diff == h_{m-r}:", verify_dd(16,3), verify_dd(16,4), verify_dd(32,3))
    # scan ALL admissible lines for given (r,n) to find the O_P MAXIMIZER and tabulate vs combinatorial guesses
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1)}
    for (r,n) in [(3,16),(4,16),(3,32)]:
        e,f=LINES[r](n); OP,nz=OP_of(n,r,e,f)
        print(f"r={r} n={n} (x^{e},x^{f}): O_P={OP}  "
              f"C(n/4,2)={comb(n//4,2)} C(n/2,r-1)={comb(n//2,r-1)} "
              f"C(n/2,r)/something... 2^(r-1)={2**(r-1)} (r-1)!={__import__('math').factorial(r-1)}")
