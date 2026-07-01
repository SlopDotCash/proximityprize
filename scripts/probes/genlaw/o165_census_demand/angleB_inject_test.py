# Angle B INJECTION test: try concrete canonical maps  gamma -> signed r-subset of mu_{n/2}
# and measure (a) injectivity, (b) image inside the K = 2^r C(n/2,r) target.
#
# Candidate maps to test (each gamma comes from a fiber of bad subsets; pick CANONICAL repr):
#
# C1 [orbit-coset]: gamma lives in a coset of <w^{e-f}>=mu_{n/d}. The O_P cosets <-> ? Not r-subset.
#
# C2 [Q-roots descent]: For a CANONICAL subset S in the gamma-fiber (lexicographically min), form
#    the interpolant Q (deg r-2) of g(z)=z^e+gamma z^f over S. R(X)=X^e+gamma X^f - Q(X) has S among
#    its roots. The r+1 roots in S... we want r objects in mu_{n/2}. Map S |-> sq(S) = {z^2} (multiset
#    in mu_{n/2}, size r+1 with multiplicity from antipodal pairs). Then DROP one canonical element
#    to get size r, sign by which preimage. Test if this is injective on gammas. (heuristic)
#
# C3 [pure subset->signed-half, then check it's a function of gamma]: define
#    Psi(S) = ( multiset {z^2 : z in S} in mu_{n/2}, sign pattern ). |S|=r+1 -> r+1 squares.
#    But target is r-subsets. Doesn't match cardinality. SKIP.
#
# REFRAME (the cardinality clue): K counts r-subsets, bad object has r+1 elements but ONE relation
# (V, codim 1) ties them => r+1 elements on a codim-1 variety ~ r free => matches r-subset count.
# The descent h_m(S)=sum h_s(SQ)h_{m-2s}(T): the TWO equations DD_r=DD_{r-1}=0 with gamma.
#
# Most promising concrete construction (test rigorously by measurement):
#   For each distinct nonzero gamma, the bilinear V + pin says the r+1 points S satisfy
#   z^e + gamma z^f = Q(z), deg Q <= r-2. Consider the SIGNED set: since e,f have fixed parities
#   relative to n/2, and squaring sends z->z^2, define for the CANONICAL (lex-min) S in fiber:
#       key(gamma) = frozenset of (z^2, indicator[z is the '+' or '-' branch]) ...
#   We instead measure the SIMPLEST possible injectivity: is gamma |-> (lex-min S in its fiber)
#   already injective (yes by construction) and does the map  S_min -> sq-multiset land in distinct
#   signed-r-subsets after canonical reduction. Rather than guess, MEASURE the count of distinct
#   sq-images and compare to #gamma and to K.

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

def signed_r_subsets_count(n,r):
    return (1<<r)*comb(n//2,r)

if __name__=="__main__":
    for (n,r,e,f) in [(16,3,8,7),(16,4,10,5),(16,5,9,15),(32,3,16,15),(32,4,18,9)]:
        fib,dom=study(n,r,e,f)
        K=signed_r_subsets_count(n,r)
        ngamma=len(fib)
        # index of element, and -z map
        idx={dom[i]:i for i in range(n)}
        neg1=dom[n//2]
        half = n//2
        # square index: dom[i]^2 = dom[(2i) mod n]; in mu_{n/2}=squares. Represent square by (2i mod n).
        # For each gamma, take lex-min S; compute multiset of square-indices; this is r+1 squares
        # (with multiplicity 2 where an antipodal pair sits). Then the "signed r-subset" reduction:
        # if a square appears twice (pair) it's ONE pair-class chosen with BOTH signs (impossible in
        # a signed r-subset of distinct pair-classes). So instead: number of DISTINCT squares = #pair-classes
        # touched. Test: is (#distinct squares) <= r typically? and does the multiset distinguish gammas?
        keys=set(); distinct_sq_dist=Counter()
        for g,subs in fib.items():
            Smin=min(subs)
            sqidx=[ (2*i)%n for i in Smin ]
            distinct_sq_dist[len(set(sqidx))]+=1
            # canonical key: sorted multiset of square-indices + which preimage (sign) chosen
            # sign: for square s = z^2, z is dom[i] or dom[i+n/2]; record i mod (n/2) gives square,
            # and the 'branch' bit = (i >= n/2)? -- but i in 0..n-1. branch = i // 1 ... use i < n/2.
            key=tuple(sorted((i % half, 1 if i>=half else 0) for i in Smin))
            keys.add(key)
        print(f"n={n} r={r}(x^{e},x^{f}): #gamma={ngamma} K={K}  #distinct lexmin-keys={len(keys)} "
              f"(inj if ==#gamma)  distinct-sq-count dist={dict(sorted(distinct_sq_dist.items()))}")
