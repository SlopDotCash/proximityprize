"""#466: measure M(mu_n)/sqrt(n) in the PRIZE regime p ~ n^beta (beta=4 Burgess barrier).
For each n=2^k pick smallest prime p >= n^beta with 2^k | p-1, and also sweep beta."""
import cmath, math
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d,r=n-1,0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def prime_ge_2adic(lo, m):
    # smallest prime p>=lo with m | p-1
    t=(lo-1+m-1)//m
    if t<1: t=1
    while True:
        p=m*t+1
        if p>=lo and is_prime(p): return p
        t+=1
def primitive_root(p):
    n=p-1; fac=set(); d=n; f=2
    while f*f<=d:
        while d%f==0: fac.add(f); d//=f
        f+=1
    if d>1: fac.add(d)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def subgroup(p,order):
    g=primitive_root(p); h=pow(g,(p-1)//order,p)
    S=[]; x=1
    for _ in range(order): S.append(x); x=x*h%p
    return S
def Mval(p,S):
    best=0.0; bb=0
    for b in range(1,p):
        s=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S))
        if s>best: best=s; bb=b
    return best,bb

for beta in (2.0, 3.0, 4.0):
    print(f"=== beta={beta} (p ~ n^beta) ===")
    for k in range(2,10):
        n=1<<k
        lo=int(n**beta)
        p=prime_ge_2adic(lo, n)
        if p>400000: 
            print(f"  k={k} n={n} p={p} SKIP(too big)"); continue
        D,bb=Mval(p, subgroup(p,n))
        print(f"  k={k} n={n:4d} p={p:7d} p/n^beta={p/n**beta:.2f} D={D:8.3f} D/sqrt(n)={D/math.sqrt(n):.3f} D/sqrt(2n)={D/math.sqrt(2*n):.3f}")
