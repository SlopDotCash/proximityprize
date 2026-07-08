"""#466: worst-case over primes. For fixed n, sweep many Burgess primes p~n^4, measure R_2,R_3.
Does max_p R_r exceed 1 (obstruction) or stay sub-Wick? Reports typical vs worst-case."""
import math
from collections import defaultdict
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
def conv(a,b,p):
    out=defaultdict(int)
    for s,cs in a.items():
        for t,ct in b.items(): out[(s+t)%p]+=cs*ct
    return out
def dfact(m):
    r=1.0
    while m>0: r*=m; m-=2
    return r
def energy(c): return sum(v*v for v in c.values())
for n in (16,32):
    lo=n**4
    primes=[]
    t=lo//n+1
    while len(primes)<300:
        p=n*t+1
        if p>=lo and is_prime(p): primes.append(p)
        t+=1
    R2s=[]; R3s=[]
    for p in primes:
        S=subgroup(p,n)
        c1=defaultdict(int)
        for x in S: c1[x]+=1
        c2=conv(c1,c1,p); c3=conv(c2,c1,p)
        sig2=n*(p-n)/(p-1)
        R2=(p*energy(c2)-n**4)/((p-1)*dfact(3)*sig2**2)
        R3=(p*energy(c3)-n**6)/((p-1)*dfact(5)*sig2**3)
        R2s.append(R2); R3s.append(R3)
    import statistics
    print(f"n={n}: {len(primes)} primes in [{primes[0]},{primes[-1]}]")
    print(f"  R_2: mean={statistics.mean(R2s):.4f} max={max(R2s):.4f} min={min(R2s):.4f}  (>1? {sum(1 for x in R2s if x>1)})")
    print(f"  R_3: mean={statistics.mean(R3s):.4f} max={max(R3s):.4f} min={min(R3s):.4f}  (>1? {sum(1 for x in R3s if x>1)})")
