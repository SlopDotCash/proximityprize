"""
probe_444_angleC_eliminant.py -- attempt a RIGOROUS degree/eliminant bound on O_P.

Reformulation: bad gamma <=> x^ebar + gamma x^fbar = P(x) on some (r+1)-subset S of mu_n,
P deg<r.  So Q_gamma(x) := x^ebar + gamma x^fbar - P(x)  has >= r+1 roots in mu_n.
Q_gamma is supported on monomials  M = {ebar, fbar} U {0..r-1}  (<= r+2 monomials), degree<n.

KEY rigorous lever to TEST: a nonzero poly with support in a fixed monomial set M of size t,
having >= (number of roots) roots in mu_n=<w>... For roots in a CYCLIC GROUP, a t-sparse poly
of degree<n can have many roots (up to n - (gap)). BUT we can use the DESCARTES/sparsity-in-
subgroup bound: # roots in mu_n of a t-sparse poly <= ??? Generally NOT bounded by t.

Alternative rigorous lever (the one that may WORK): count bad gamma via the resultant of the
TWO equations that pin (S, gamma):
   det M(S)=0  (V, the variety)  and  gamma h_{f-r}(S)+h_{e-r}(S)=0 (gamma pin).
Eliminate S? S is discrete (a subset), not a continuous variable, so classical elimination
doesn't directly apply.  Instead, the RIGHT object: gamma is bad iff the
   (r+2)-term "generalized Vandermonde"  has an (r+1)-subset dependency.

We TEST the following concrete COUNT that IS provable-looking:
  Consider the polynomial  R(T) = prod over gamma-orbit-reps (T - gamma^{n/d}).  Its degree is O_P.
  Is R(T) a FACTOR of an explicitly-constructed resultant whose degree we can bound a-priori?

Most tractable test: the bad gamma are roots (in T=gamma) of the univariate polynomial
  Phi(T) = Res_x( numerator stuff )... we instead directly MEASURE: is the set {gamma} the root
  set of a poly of degree exactly O_P whose coefficients are symmetric in mu_n => Galois-stable
  => O_P is a sum of mu_n-orbit sizes / the structure is rigid.

This probe checks a SPECIFIC provable upper bound candidate:
  O_P <= (number of monomials in the 'defect' poly) choose 2 * something, OR
  O_P <= deg of the Wronskian-like obstruction.
We compute, for each line, O_P and compare to:  (e-r)+(f-r) , (e-r)*(f-r)/n-ish, |M| etc.
to find what algebraic degree quantity tracks O_P (to identify the right Bezout bound).
"""
import sys
from math import comb, gcd
from itertools import combinations

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

def OP_of(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    cos=set()
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: cos.add(pow(g,nd,p))
    return len(cos),d,nd

if __name__=="__main__":
    print("track O_P against algebraic-degree quantities (to find the Bezout handle):")
    print(f"{'r':>2}{'n':>4}{'e':>3}{'f':>3}{'d':>3}{'O_P':>5}  {'ebar':>4}{'fbar':>4} {'(er)(fr)':>9} {'min(er,fr)':>10} {'C(n/2,r-1)':>11}")
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    for (r,n) in [(3,16),(4,16),(5,16),(6,16),(3,32)]:
        # scan a few lines, including maximizer
        e0,f0=LINES[r](n)
        lines=[(e0,f0),(n-1,r),(r,r+1),(n//2,r)]
        for (e,f) in lines:
            if e<r or f<r or e==f or e>=n+r or f>=n+r: continue
            OP,d,nd=OP_of(n,r,e,f)
            er,fr=e-r,f-r
            print(f"{r:>2}{n:>4}{e:>3}{f:>3}{d:>3}{OP:>5}  {e%n:>4}{f%n:>4} {er*fr:>9} {min(er,fr):>10} {comb(n//2,r-1):>11}")
