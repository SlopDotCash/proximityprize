# Sigma-pattern of bad subsets across r. sigma(z)=z^{n/2} in {+1,-1} (square/nonsquare).
# At r=3 every bad 4-subset was perfectly 2 squares + 2 nonsquares. Does a uniform balanced
# signature persist? Test on the TRUE maximizer lines (small n, exact).
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
    lines=[(16,4,10,5),(16,5,9,15),(16,6,12,10)]
    for (n,r,e,f) in lines:
        fib,dom=collect(n,r,e,f)
        sig=[1 if pow(dom[i],n//2,p)==1 else -1 for i in range(n)]
        # per gamma, take ALL subsets in fiber; record #squares in each
        nsq_dist=Counter()
        # also: is #squares constant across a gamma's fiber?
        const=0; vary=0
        for g,subs in fib.items():
            cnts=set()
            for S in subs:
                ns=sum(1 for i in S if sig[i]==1); nsq_dist[ns]+=1; cnts.add(ns)
            if len(cnts)==1: const+=1
            else: vary+=1
        print(f"n={n} r={r}(x^{e},x^{f}): #gamma={len(fib)} | #squares-per-subset dist={dict(sorted(nsq_dist.items()))} | #sq const-on-fiber:{const} vary:{vary}")
        # exponent-parity of e,f relative to n/2
        print(f"    e={e}(e%2={e%2}) f={f}(f%2={f%2}) | e-f={e-f}")
