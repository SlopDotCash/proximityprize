"""
probe_444_boundB_r3symbolic.py -- GENUINE symbolic elimination for r=3, to read off the eliminant
degree and SEE the antipodal-descent 2^r factor concretely.

r=3 CLEAN MODEL (proven): 4-subset S={a,b,c,d} of mu_n is bad iff {a,b} in mu_{n/2} (squares),
{c,d} in nonsquares, and a*b = -c*d.  gamma = -h_{e-3}(S)/h_{f-3}(S).

ELIMINATION QUESTION.  Fix the maximizer line (e,f). gamma is a rational function of (a,b,c,d) on
the variety {a^{n/2}=1, b^{n/2}=1, (c)^{...}=nonsquare, ab+cd=0}.  How many distinct gamma^{n/d}?

The squares subgroup mu_{n/2} has size n/2.  A square pair {a,b} is an unordered pair of mu_{n/2}
elements => C(n/2,2) choices.  Given {a,b}, the product ab=-cd is FIXED, and {c,d} nonsquares with
cd = -ab; the number of nonsquare pairs with a given product is ~ (n/2)/2 = n/4 ... but gamma may
not depend on the choice.  We compute the elimination degree EXACTLY (symbolically in roots of
unity) for small n and read the n-dependence.

We do it concretely over F_p (exact) but track the COUNT as a function that should be a binomial
in n/2 if the descent is genuine.  KEY metric: the eliminant degree O_P, decomposed.
"""
import sympy as sp
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

def r3_structured(n,e,f,p=P):
    """Enumerate ONLY structured 4-subsets (2 squares + 2 nonsquares, ab=-cd) and compute gamma.
       Compare J-set to the brute one. Also tally: for each square-pair {a,b}, how many distinct J
       arise (over the compatible nonsquare pairs)?  This is the per-(square-pair) FIBER count =
       the residual the elimination must bound."""
    w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    sq=[pow(w,2*i,p) for i in range(n//2)]       # squares = even indices
    nsq=[pow(w,2*i+1,p) for i in range(n//2)]     # nonsquares = odd indices
    M=max(e-3+1,f-3+1)
    # map: square-pair (as index pair) -> set of J
    from collections import defaultdict
    pairJ=defaultdict(set)
    allJ=set()
    sqi=[2*i for i in range(n//2)]
    nsqi=[2*i+1 for i in range(n//2)]
    for (ia,ib) in combinations(range(n//2),2):
        a,b=sq[ia],sq[ib]
        prod=(a*b)%p
        target=(-prod)%p   # need c*d = -a*b
        for (ic,idx) in combinations(range(n//2),2):
            c,d=nsq[ic],nsq[idx]
            if (c*d)%p!=target: continue
            S=[a,b,c,d]
            H=hpow(S,M,p)
            if (H[e-3]*H[f-3+1]-H[f-3]*H[e-3+1])%p: continue   # double-check on V
            if H[f-3]==0: continue
            g=(-H[e-3]*pow(H[f-3],p-2,p))%p
            if not g: continue
            J=pow(g,nd,p)
            pairJ[(ia,ib)].add(J); allJ.add(J)
    fibers=[len(v) for v in pairJ.values()]
    return len(allJ), len(pairJ), (min(fibers) if fibers else 0), (max(fibers) if fibers else 0)

if __name__=="__main__":
    print("r=3 structured (2sq+2nsq, ab=-cd) elimination decomposition:")
    print(f"{'n':>4} {'O_P':>5} {'#sqpairs w/sol':>15} {'fiber(min,max)':>16} {'C(n/2,2)':>9} {'C(n/4,2)':>9}")
    for n in [16,32,64]:
        e,f=n//2,n//2-1
        OP, npairs, fmin, fmax = r3_structured(n,e,f)
        print(f"{n:>4} {OP:>5} {npairs:>15} {('('+str(fmin)+','+str(fmax)+')'):>16} "
              f"{comb(n//2,2):>9} {comb(n//4,2):>9}")
