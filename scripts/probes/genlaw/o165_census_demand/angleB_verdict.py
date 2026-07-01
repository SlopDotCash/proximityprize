# FINAL: characterize exactly where the Angle-B injection succeeds vs collides.
# r=3: PROVEN clean (closed form n*C(n/4,2), bijection gamma<->tuple, <K).
# r=4: sigma(#squares) CONSTANT on gamma fibers (144/144) -> a sigma-graded invariant survives.
# r>=5: sigma NOT constant on some fibers -> the sigma-branch sign map is NOT well-defined on gamma.
#
# Here: (1) For r=4, build the candidate injection gamma -> (sigma-signature, squared-elem-symm)
#         and test injectivity + landing in K.
#      (2) For r=5,6, EXHIBIT an explicit collision: two bad subsets with DIFFERENT sigma-signature
#         but the SAME gamma (the exact obstruction), to document why the natural injection fails.
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
    # (2) explicit r=5 collision
    print("=== r>=5 COLLISION (different sigma-signature, same gamma) ===")
    for (n,r,e,f) in [(16,5,9,15),(16,6,12,10)]:
        fib,dom=collect(n,r,e,f)
        sig=[1 if pow(dom[i],n//2,p)==1 else -1 for i in range(n)]
        found=0
        for g,subs in fib.items():
            sigs=set(tuple(sorted(sig[i] for i in S)) for S in subs)
            nsqs=set(sum(1 for i in S if sig[i]==1) for S in subs)
            if len(nsqs)>1:
                S0,S1=None,None
                seen={}
                for S in subs:
                    ns=sum(1 for i in S if sig[i]==1)
                    if ns in seen: continue
                    seen[ns]=S
                ks=sorted(seen)
                print(f"  n={n} r={r}: gamma={g} has subsets with #squares={ks}: "
                      f"S(#sq={ks[0]})={seen[ks[0]]}  S(#sq={ks[-1]})={seen[ks[-1]]}")
                found+=1
                if found>=2: break
    # (1) r=4 injection: sigma-signature constant; try gamma -> (nsq, sorted squared-pair-sums)
    print("\n=== r=4 injection candidate ===")
    for (n,r,e,f) in [(16,4,10,5),(32,4,18,9)]:
        fib,dom=collect(n,r,e,f)
        sig=[1 if pow(dom[i],n//2,p)==1 else -1 for i in range(n)]
        K=(1<<r)*comb(n//2,r)
        # invariant: for lex-min S, (#squares, multiset of square-indices/2, multiset nonsq) ...
        # test the SIMPLEST: is gamma -> sorted(sigma-pattern over index) i.e. the SET of indices'
        # square/2 structure injective? We just confirm #gamma<=K and #gamma value.
        # Build map gamma -> ( tuple sorted( (i mod (n//2)) for i in lexmin S ), sign bits )
        half=n//2; keys=Counter()
        coll=0
        seen={}
        for g,subs in fib.items():
            S=min(subs)
            key=tuple(sorted((i%half, 1 if sig[i]==1 else 0) for i in S))
            if key in seen: coll+=1
            seen[key]=g
            keys[key]+=1
        print(f"  n={n} r={r}: #gamma={len(fib)} K={K} bad/K={len(fib)/K:.4f}  "
              f"lexmin-sigkey injective? {coll==0} (collisions={coll})")
