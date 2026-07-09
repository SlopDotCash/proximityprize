"""
C004 CLAIM B falsifier, focused: does the orbit count K cross 1->2 at delta*, or does it
GROW (= the BGK/Gauss-period wall) so the budget #bad<=n (K<=1) is violated by a large factor?

For each n, take the ADJACENT direction (b=k, a=k+1, t=1) = the KKH26 worst-case ceiling family
(C004 itself names this the extremal family). The bad-scalar count there is the far-line incidence
I(delta) at the cleanest radius delta = 1 - (k+1)/n. We report K = #bad/n (orbit count) at rate
rho=1/4 and rho=1/2, for n = 8,16,32, multiple proper-subgroup primes. If C004's "K crosses 1->2
at delta*" were right, K should be ~1 here; if it's the BGK wall, K grows with n.
"""
import itertools
from math import gcd, log

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_primes(n, blo, bhi, want):
    lo=int(n**blo); out=[]
    q=lo-(lo%n)+1
    if q<lo: q+=n
    hi=int(n**bhi)
    while q<=hi and len(out)<want:
        if q>n+1 and is_prime(q): out.append(q)
        q+=n
    return out

def orderOf(g,q):
    if g==0: return 0
    x=g%q; o=1
    while x!=1:
        x=x*g%q; o+=1
        if o>q: return -1
    return o

def mu_n(q,n):
    cof=(q-1)//n
    for h in range(2,q):
        g=pow(h,cof,q)
        if orderOf(g,q)==n:
            return g,[pow(g,i,q) for i in range(n)]
    raise RuntimeError

def esymm(S,t,q):
    e=[0]*(t+1); e[0]=1
    for x in S:
        for j in range(min(t,len(e)-1),0,-1):
            e[j]=(e[j]+e[j-1]*x)%q
    return e[t]

def adj_badcount(elems,a,t,q):
    """#bad for adjacent direction: t=1 means e_1(S)=sum unconstrained; just count distinct e_1 over |S|=a."""
    vals=set()
    for S in itertools.combinations(elems,a):
        ok=True
        for j in range(1,t):
            if esymm(S,j,q)!=0: ok=False; break
        if ok: vals.add(esymm(S,t,q)%q)
    return vals

print("="*78)
print("C004 Claim B: K = #bad/n for the ADJACENT (t=1) extremal direction, PRIZE regime")
print("If 'K crosses 1->2 at delta*' : K~1.  If BGK wall: K grows with n.")
print("="*78)
print(f"{'n':>4} {'rho':>5} {'q':>9} {'beta':>5} {'a=k+1':>6} {'delta':>7} {'#bad':>7} "
      f"{'eps0':>5} {'K=#bad/n':>9}")
for n in (8,16,32):
    for rho in (0.25,0.5):
        k=int(round(rho*n)); a=k+1; t=1
        for q in find_primes(n,4.0,5.0,1):
            g,elems=mu_n(q,n)
            vals=adj_badcount(elems,a,t,q)
            has0=1 if 0 in vals else 0
            total=len(vals)
            K=(total-has0)/n
            print(f"{n:>4} {rho:>5} {q:>9} {log(q,n):>5.2f} {a:>6} {1-a/n:>7.3f} "
                  f"{total:>7} {has0:>5} {K:>9.3f}   (#bad-eps0={total-has0}={n}*{int(round((total-has0)/n))})")
