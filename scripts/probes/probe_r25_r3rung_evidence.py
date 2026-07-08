"""#466 decisive evidence for the first OPEN rung r=3: does R_3 cross 1 or saturate below?
E_{2r} = sum_s c_r(s)^2, c_r = r-fold convolution of indicator(mu_n) mod p (fast, no p-loop).
S_r = p*E_{2r} - n^{2r};  sigma^2 = n(p-n)/(p-1);  R_r = S_r/((p-1)(2r-1)!! sigma^{2r})."""
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
def prime_ge_2adic(lo,m):
    t=max(1,(lo-1+m-1)//m)
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
def conv(a,b,p):
    out=defaultdict(int)
    for s,cs in a.items():
        for t,ct in b.items():
            out[(s+t)%p]+=cs*ct
    return out
def dfact(m):
    r=1.0
    while m>0: r*=m; m-=2
    return r
def energy(c):  # sum c(s)^2
    return sum(v*v for v in c.values())
print("R_r for r=2,3,4 (Burgess beta=4) — watch R_3 for crossing 1:")
for k in range(3,9):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    S=subgroup(p,n)
    c1=defaultdict(int)
    for x in S: c1[x]+=1
    c2=conv(c1,c1,p)
    if n<=2048:
        c3=conv(c2,c1,p)
    sig2=n*(p-n)/(p-1)
    def R(r,c): 
        Sr=p*energy(c)-n**(2*r); return Sr/((p-1)*dfact(2*r-1)*sig2**r)
    r2=R(2,c2); r3=R(3,c3)
    print(f"  n={n:4d} p={p:11d}  R_2={r2:.4f}  R_3={r3:.4f}")
