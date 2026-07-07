# Angle B GENERAL r: the honest test of whether ANY canonical injection
#   {distinct nonzero gamma} -> {signed r-subsets of mu_{n/2}}  exists with a PROVABLE bound.
#
# The r=3 success used: bad 4-subset = 2 squares + 2 nonsquares with ab=-cd; gamma <-> tuple
# bijective; #bad = n C(n/4,2) < K. The mechanism: deficit-2 codeword deg = r-2 = 1, the
# interpolant Q is deg<=r-2. For general r, Q has degree r-2 and the bad S are the (r+1)-subsets
# on which z^e+gamma z^f - Q(z) vanishes; Q has r-1 coefficients but only r-2 effective DOF since
# its two top conditions are pinned.
#
# THE CLEAN GENERAL HANDLE (test): roots-of-R. R_gamma,Q(X) = X^e + gamma X^f - Q(X), deg=e<=n.
# S subset roots(R). The NUMBER of distinct gamma is at most #distinct R's with >=r+1 roots in mu_n.
# Bound via: each gamma + the deg<=r-2 Q gives a polynomial; distinct bad gamma <= #such polys with
# >= r+1 mu_n-roots. Hard.
#
# So instead, EMPIRICALLY answer the load-bearing question for the prize:
#   Is there a SIMPLE invariant I(S) (a signed r-subset of mu_{n/2}) such that
#     (a) I is constant on each gamma-fiber  (=> well-defined map gamma -> signed r-subset), AND
#     (b) I is injective on distinct gammas, AND
#     (c) I lands in the 2^r C(n/2,r) target,
#   OR a bounded-to-one version. We test several natural I and report which property fails.
#
# Natural candidate invariants (functions of the bad subset S, hopefully gamma-fiber-invariant):
#  I1 = the deg<=r-2 interpolant Q's coefficient vector (NOT fiber-invariant per earlier: r=5 varied)
#  I2 = the multiset sq(S)={z^2} in mu_{n/2} (size r+1) -- NOT a signed r-subset (wrong card)
#  I3 = gamma itself + a tiebreak.  (gamma is the object; need to map INTO signed r-subsets.)
#
# KEY realization to test: maybe the right statement is the WEAKER, still-sufficient bound
#     #distinct gamma  <=  #{ (r-1)-subsets of mu_{n/2} } * 2^{?}  or directly  <= K
#   provable by  gamma -> (e_1..e_{?} of the squared roots).  Let's measure, for the TRUE maximizer
#   lines, the map  gamma -> (canonical lex-min bad S) -> sq-elementary-symmetric data, and check
#   how many distinct gammas collide under coarse invariants vs K.
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
def collect(n,r,e,f):
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
    lines=[(16,4,10,5),(32,4,18,9),(16,5,9,15),(16,6,12,10),(32,6,20,16)]
    for (n,r,e,f) in lines:
        fib,dom=collect(n,r,e,f)
        K=(1<<r)*comb(n//2,r)
        ngamma=len(fib); d=gcd(e-f,n)
        # canonical S per gamma = lex-min. Compute squared-elementary symmetrics e_1..e_r of sq(S)
        # restricted: take sq(S) (multiset of r+1 squares), and the (r)-subset = drop the unique
        # element making product canonical? Instead, test the coarsest: does gamma -> (e1,..,e_{r-1})
        # of sq(lex-min S) re-inject? We mostly want to know: is #gamma <= K (already known true) and
        # whether a NATURAL gamma-fiber-invariant lands injectively in <=K classes.
        # Measure: #distinct values of  (sorted multiset sq(S_lexmin))  across gammas:
        sqkeys=set()
        for g,subs in fib.items():
            S=min(subs)
            sqms=tuple(sorted((2*i)%n for i in S))   # squares as indices in 0..n-1 step2 (mu_{n/2} ~ index/2)
            sqkeys.add((g, ))  # placeholder
        # The real diagnostic: count gammas, and the THEORETICAL signed-r-subset count K, ratio.
        print(f"n={n} r={r}(x^{e},x^{f}) d={d}: #gamma={ngamma}  K={K}  bad/K={ngamma/K:.4f}  "
              f"fiberdist={dict(sorted(Counter(len(v) for v in fib.values()).items()))}")
