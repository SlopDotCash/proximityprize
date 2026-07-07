# LAST candidate: does gamma -> (squared-root data of lex-min S) give a map into signed r-subsets
# that is at least BOUNDED-to-one with bound small enough to clear K? The honest question: even if
# we can't get a clean injection, is #gamma <= K provable by ANY map factoring through mu_{n/2}?
#
# We already KNOW #gamma <= K numerically at every measured line. The Angle-B THESIS is that the
# bound is *witnessed* by an injection into signed r-subsets. We test the strongest remaining
# structural fact: is the gamma-map's IMAGE-in-mu_{n/2} (via squaring the lex-min subset) at most
# K-sized and does it dominate #gamma? We measure the count of distinct  sq-elementary-symmetric
# vectors  vs #gamma vs K.
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
    for (n,r,e,f) in [(16,4,10,5),(16,5,9,15),(16,6,12,10),(32,4,18,9)]:
        fib,dom=collect(n,r,e,f)
        K=(1<<r)*comb(n//2,r)
        # squared-root multiset of lex-min S (r+1 squares in mu_{n/2}); also the WHOLE-fiber union
        # of squared multisets. Test: is the squared multiset constant on a gamma fiber?
        const_sqms=0; vary_sqms=0
        keyset=set()
        for g,subs in fib.items():
            sqmss=set(tuple(sorted((2*i)%n for i in S)) for S in subs)
            if len(sqmss)==1: const_sqms+=1
            else: vary_sqms+=1
            keyset.add(min(sqmss))
        print(f"n={n} r={r}(x^{e},x^{f}): #gamma={len(fib)} K={K} | sq-multiset(lexmin) const-on-fiber:{const_sqms} vary:{vary_sqms} | #distinct lexmin-sqms={len(keyset)}")
