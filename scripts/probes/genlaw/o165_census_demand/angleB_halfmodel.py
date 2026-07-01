# Angle B: does the WHOLE bad-gamma census descend to a census on the HALF mu_{n/2}?
#
# Observation: gamma = -h_{e-r}(S)/h_{f-r}(S) and the bad condition is a symmetric-function
# identity. Use the descent h_m(S) = sum_s h_s(SQ) h_{m-2s}(T), SQ=pair-squares in mu_{n/2},
# T=singletons in mu_n. Split S into c antipodal pairs and (r+1-2c) singletons.
#
# If S is a UNION OF ANTIPODAL PAIRS (no singletons, needs r+1 even): then T empty, h_m(S)=h_{m/2}(SQ)
# if m even else 0. Then h_{e-r}(S)=0 unless e-r even; etc. The whole thing becomes a census on
# mu_{n/2} at HALF the indices => an r' = (r+1)/2-ish recursion. This is the recursion that would
# yield the 2^r factor by tracking the sign/branch of each singleton.
#
# GOAL: empirically decompose #bad and K by the antipodal type (c = #pairs) of the subsets, and
# see if a per-type injection into 2^{#singletons} * (half subsets) is plausible.

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
    idx={dom[i]:i for i in range(n)}; neg1=dom[n//2]
    # gamma -> list of (c=#pairs, S)
    fib={}
    for S in combinations(range(n),a):
        elts=[dom[i] for i in S]; H=h_ps(elts,mmax)
        he,hf,he1,hf1=H[me],H[mf],H[me1],H[mf1]
        if (he*hf1-hf*he1)%p: continue
        if hf%p==0: continue
        g=(-he*inv(hf))%p
        if g==0: continue
        Sset=set(S); seen=set(); c=0
        for i in S:
            if i in seen: continue
            j=idx[(dom[i]*neg1)%p]
            if j in Sset: c+=1; seen.add(i); seen.add(j)
            else: seen.add(i)
        fib.setdefault(g,[]).append((c,tuple(S)))
    return fib,dom

if __name__=="__main__":
    for (n,r,e,f) in [(16,3,8,7),(16,4,10,5),(16,5,9,15),(32,3,16,15)]:
        fib,dom=study(n,r,e,f)
        K=(1<<r)*comb(n//2,r)
        # For each gamma, the set of c-values in its fiber; and overall distribution of (subset c)
        subset_c=Counter()
        gamma_minc=Counter()  # the min c over the fiber, as a 'type' of the gamma
        for g,lst in fib.items():
            cs=[c for c,_ in lst]
            for c in cs: subset_c[c]+=1
            gamma_minc[min(cs)]+=1
        print(f"n={n} r={r}(x^{e},x^{f}): #gamma={len(fib)} K={K}")
        print(f"    subset antipodal-type c=#pairs dist: {dict(sorted(subset_c.items()))}")
        print(f"    per-gamma MIN-c dist: {dict(sorted(gamma_minc.items()))}")
        # K decomposition by #pairs: a signed r-subset of mu_{n/2} has 0 'pairs' by definition.
        # But the bad SUBSETS have c pairs. The 2^r counts sign choices = singleton branches.
        # Pure-singleton bad subsets (c=0): these are r+1 distinct pair-classes all single-signed.
        # Count them vs C(n/2, r+1)*2^{r+1}:
