"""
C004 Claim B at n=32 (dyadic, proper subgroup) via size-constrained subset-sum DP — no brute force.
t=1 adjacent direction: bad set = { sum_{x in S} x mod q : S subset of mu_n, |S| = a }, a=k+1.
K = (#distinct sums excluding the 0-sum-if-present)/n  (orbit count). Wall-test: does K grow?
"""
from math import log

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_prime(n,blo,bhi):
    lo=int(n**blo); q=lo-(lo%n)+1
    if q<lo: q+=n
    while q<=int(n**bhi):
        if q>n+1 and is_prime(q): return q
        q+=n
    return None

def orderOf(g,q):
    if g==0: return 0
    x=g%q;o=1
    while x!=1:
        x=x*g%q;o+=1
        if o>q: return -1
    return o

def mu_n(q,n):
    cof=(q-1)//n
    for h in range(2,q):
        g=pow(h,cof,q)
        if orderOf(g,q)==n:
            return g,[pow(g,i,q) for i in range(n)]
    raise RuntimeError

def distinct_sums_of_size(elems,a,q):
    """all values sum(S) mod q for S subset of elems, |S|=a, via DP layered by chosen-count."""
    # layers[j] = set of achievable sums using exactly j chosen elements so far
    layers=[set() for _ in range(a+1)]
    layers[0].add(0)
    for x in elems:
        for j in range(min(a,len(elems)),0,-1):
            if layers[j-1]:
                lj=layers[j]
                for s in layers[j-1]:
                    lj.add((s+x)%q)
    return layers[a]

print("="*70)
print("C004 Claim B at n=32 (dyadic proper subgroup) — adjacent t=1, K=#bad/n")
print("="*70)
n=32
for rho in (0.25,0.5):
    k=int(round(rho*n)); a=k+1
    q=find_prime(n,4.0,4.6)
    g,elems=mu_n(q,n)
    sums=distinct_sums_of_size(elems,a,q)
    has0=1 if 0 in sums else 0
    total=len(sums)
    K=(total-has0)/n
    print(f"n={n} rho={rho} q={q} beta={log(q,n):.2f} a=k+1={a} delta={1-a/n:.3f} "
          f"#bad={total} eps0={has0} K=#bad/n={K:.2f}  (#bad-eps0={total-has0}={n}*{(total-has0)//n})")
print("\nCompare to proven budget: q*eps* ~ n  <=>  K<=1.  Observed K:")
