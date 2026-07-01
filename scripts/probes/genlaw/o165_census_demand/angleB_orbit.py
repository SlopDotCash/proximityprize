# Angle B: the dilation-orbit structure of {distinct nonzero gamma} and the injection counting.
#
# gamma(gS) = g^{e-f} gamma(S), g in mu_n. So gamma is a section of a line bundle; the set of
# bad gammas is a UNION of orbits under g |-> g^{e-f} * (.), each orbit = a coset of <w^{e-f}> =
# <w^d>... actually multiplying by g^{e-f} as g ranges over mu_n gives the subgroup
# <w^{e-f}> = mu_{n/d}, d=gcd(e-f,n). So the gammas group into mu_{n/d}-COSETS, each of size n/d.
# #bad(nz) = (n/d) * O_P. The INJECTION target K = 2^r C(n/2,r).
#
# Reframed injection (the natural one): map each ORBIT-of-gammas (there are O_P of them) ...
# no, we must inject EACH gamma. Equivalent: inject (n/d)*O_P gammas into K signed r-subsets.
#
# DIRECT TEST OF ANGLE B as literally stated: build the map
#    Psi: bad-subset S  -->  signed r-subset of mu_{n/2}
# and check it FACTORS THROUGH gamma (i.e. constant on gamma-fibers is FALSE since fibers vary),
# OR build  Phi: gamma --> signed r-subset and check injective.  We need a CANONICAL signed
# r-subset from gamma alone.
#
# Idea from the binomial interpolant Q(X)=X^2 + (gamma-dependent) X observed at r=4:
# more generally Q has degree <= r-2? Let's measure the interpolant degree distribution and
# its ROOTS for general r, and whether the roots (a signed multiset in mu_n) descend to mu_{n/2}.

from math import comb, gcd
from itertools import combinations
from collections import Counter

p = 2013265921
def inv(x): return pow(x,p-2,p)
def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
    raise RuntimeError
def h_ps(elts,mmax):
    L=len(elts);P=[L%p]+[0]*mmax;cur=[1]*L
    for i in range(1,mmax+1):
        s=0
        for j in range(L): cur[j]=(cur[j]*elts[j])%p; s+=cur[j]
        P[i]=s%p
    H=[1]+[0]*mmax
    for m in range(1,mmax+1):
        acc=0
        for i in range(1,m+1): acc=(acc+P[i]*H[m-i])%p
        H[m]=(acc*inv(m))%p
    return H
def interp_coeffs(pts,vals):
    m=len(pts);M=[[pow(pts[i],j,p) for j in range(m)]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]; iv=inv(M[col][col]); M[col]=[(v*iv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p: fc=M[rr][col]; M[rr]=[(M[rr][k]-fc*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]

def study(n,r,e,f):
    dom=mu_n(n); a=r+1
    me,mf,me1,mf1=e-r,f-r,e-r+1,f-r+1
    mmax=max(me,mf,me1,mf1)
    fib={}
    for S in combinations(range(n),a):
        elts=[dom[i] for i in S]; H=h_ps(elts,mmax)
        he,hf,he1,hf1=H[me],H[mf],H[me1],H[mf1]
        if (he*hf1-hf*he1)%p: continue
        if hf%p==0: continue
        g=(-he*inv(hf))%p
        if g==0: continue
        fib.setdefault(g,[]).append(tuple(S))
    return fib,dom

if __name__=="__main__":
    for (n,r,e,f) in [(16,3,8,7),(16,4,10,5),(16,5,9,15),(32,3,16,15)]:
        fib,dom=study(n,r,e,f)
        d=gcd(e-f,n); nd=n//d
        # interpolant-degree distribution over all bad subsets
        degdist=Counter()
        # also: for each gamma, the interpolant Q's coeff vector (canonical?) — is it
        # constant across the fiber? Check.
        gamma_Qconst=0; gamma_Qvary=0
        for g,subs in fib.items():
            Qs=set()
            for S in subs:
                pts=[dom[i] for i in S]; vals=[(pow(dom[i],e,p)+g*pow(dom[i],f,p))%p for i in S]
                c=interp_coeffs(pts,vals)
                deg=max([j for j in range(len(c)) if c[j]],default=-1)
                degdist[deg]+=1
                Qs.add(tuple(c))
            if len(Qs)==1: gamma_Qconst+=1
            else: gamma_Qvary+=1
        print(f"n={n} r={r} (x^{e},x^{f}) d={d}: #gamma={len(fib)} degdist={dict(sorted(degdist.items()))} "
              f"Q-const-on-fiber:{gamma_Qconst} Q-varies:{gamma_Qvary}")
