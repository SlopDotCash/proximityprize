# Decode the TRUE r=3 bad-subset condition from brute force. Earlier probe said every bad 4-subset
# has exactly 2 squares (sigma=+1) and 2 nonsquares. Let's extract the actual (2 squares, 2 nonsq)
# and find the real relation among their exponents.
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

def bad_r3(n):
    dom=mu_n(n); e,f=n//2,n//2-1
    me,mf,me1,mf1=e-3,f-3,e-2,f-2
    mmax=max(me,mf,me1,mf1)
    fib={}
    for S in combinations(range(n),4):
        elts=[dom[i] for i in S]; H=h_ps(elts,mmax)
        he,hf,he1,hf1=H[me],H[mf],H[me1],H[mf1]
        if (he*hf1-hf*he1)%p: continue
        if hf%p==0: continue
        g=(-he*inv(hf))%p
        if g==0: continue
        fib.setdefault(g,[]).append(tuple(S))
    return fib,dom

if __name__=="__main__":
    for n in [16]:
        fib,dom=bad_r3(n)
        sig=[1 if pow(dom[i],n//2,p)==1 else -1 for i in range(n)]
        # for each bad subset, exponents (the index i = log_w), squares = even index, nonsq=odd
        print(f"n={n}: #gamma={len(fib)}")
        # examine exponent multiset of bad subsets
        rel=Counter()
        for g,subs in fib.items():
            S=subs[0]
            sq=[i for i in S if sig[i]==1]; ns=[i for i in S if sig[i]==-1]
            # try relation among indices: sum of squares idx vs nonsq idx mod n
            ssq=sum(sq)%n; sns=sum(ns)%n
            rel[(len(sq),len(ns),(ssq-sns)%n)]+=1
        print("  (#sq,#ns,(sumSqIdx-sumNsIdx) mod n) dist:", dict(sorted(rel.items())))
        # also product relation: prod of sq elements vs prod nonsq
        rel2=Counter()
        for g,subs in fib.items():
            S=subs[0]
            sq=[i for i in S if sig[i]==1]; ns=[i for i in S if sig[i]==-1]
            psq=1;
            for i in sq: psq=(psq*dom[i])%p
            pns=1
            for i in ns: pns=(pns*dom[i])%p
            rel2[(psq==pns, (psq*inv(pns))%p in set(dom))]+=1
        # what is prod_sq / prod_ns ? express as power of w
        wlog={dom[i]:i for i in range(n)}
        ratios=Counter()
        for g,subs in fib.items():
            S=subs[0]
            sq=[i for i in S if sig[i]==1]; ns=[i for i in S if sig[i]==-1]
            psq=1
            for i in sq: psq=(psq*dom[i])%p
            pns=1
            for i in ns: pns=(pns*dom[i])%p
            r=(psq*inv(pns))%p
            ratios[wlog.get(r,'?')]+=1
        print("  prod_sq/prod_ns as w-power dist:", dict(sorted(ratios.items(), key=lambda kv:(str(kv[0])))))
        # show a few raw bad subsets with sigma pattern
        for g,subs in list(fib.items())[:4]:
            S=subs[0]
            print(f"   gamma={g} S={S} sig={[sig[i] for i in S]} idxsq={[i for i in S if sig[i]==1]} idxns={[i for i in S if sig[i]==-1]}")
