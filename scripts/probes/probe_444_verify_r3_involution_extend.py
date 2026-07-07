"""
Extend the CALIBRATED involution count (with exclusions a!=+-1, c^2!=-1, matching the true O_P
at n=16,32) out to large n, and ALSO directly test whether the involution map
  phi:(s1,s2)->(s1+s2)^2  on S1* x S2*  is EXACTLY 2-to-1 (fiber sizes) for all n.
This is the ONLY step in the BoundA r=3 argument that is 'verified up to n=256' rather than proven.
We push it as far as memory allows and look for ANY fiber != 2 (which would break the involution count).
We separately confirm |S1*|=n/4-1, |S2*|=n/4 -> image C(n/4,2) iff strictly 2-to-1.
"""
from math import comb
from collections import defaultdict
PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,4000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def inv(a,p): return pow(a,p-2,p)
def sets(n,p):
    w=gen(n,p)
    sq=[pow(w,2*i,p) for i in range(n//2)]; ns=[pow(w,2*i+1,p) for i in range(n//2)]
    S1=set()
    for a in sq:
        if a==1 or a==p-1: continue          # exclude a=+-1
        S1.add((a+inv(a,p))%p)
    S2=set()
    for c in ns:
        if (c*c)%p==p-1: continue            # exclude c^2=-1
        S2.add((c-inv(c,p))%p)
    return sorted(S1),sorted(S2)
def check(n,p):
    S1,S2=sets(n,p)
    # fiber sizes of phi without building full product when huge: use a dict of value->count
    cnt=defaultdict(int)
    badfiber=False
    for s1 in S1:
        for s2 in S2:
            v=((s1+s2)%p)*((s1+s2)%p)%p
            cnt[v]+=1
    sizes=set(cnt.values())
    image=len(cnt)
    # verify negation-closure giving the 2-to-1
    setS1=set(S1); setS2=set(S2)
    negclosed = all(((-s)%p) in setS1 for s in S1) and all(((-s)%p) in setS2 for s in S2)
    return len(S1),len(S2),image,sizes,negclosed
if __name__=="__main__":
    p=PRIMES[0]
    for n in [16,32,64,128,256,512,1024,2048,4096,8192]:
        nS1,nS2,image,sizes,negc=check(n,p)
        C=comb(n//4,2)
        print(f"n={n}: |S1*|={nS1}(n/4-1={n//4-1}) |S2*|={nS2}(n/4={n//4}) image={image} C(n/4,2)={C} match={image==C} fibersizes={sizes} negClosed={negc}")
