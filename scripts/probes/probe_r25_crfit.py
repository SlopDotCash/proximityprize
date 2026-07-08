"""#466: test conjecture R_r = 1 - C(r,2)/n + O((r^2/n)^2) for r=2..5, dyadic mu_n, Burgess beta=4.
c_r := n*(1-R_r) should -> C(r,2) = r(r-1)/2."""
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
        for t,ct in b.items(): out[(s+t)%p]+=cs*ct
    return out
def dfact(m):
    r=1.0
    while m>0: r*=m; m-=2
    return r
def energy(c): return sum(v*v for v in c.values())
print("c_r := n*(1-R_r)  vs  C(r,2)=r(r-1)/2  [predict 1,3,6,10 for r=2,3,4,5]")
for k in (5,6,7):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    S=subgroup(p,n)
    c1=defaultdict(int)
    for x in S: c1[x]+=1
    c2=conv(c1,c1,p); c3=conv(c2,c1,p); c4=conv(c2,c2,p); c5=conv(c4,c1,p)
    sig2=n*(p-n)/(p-1)
    def cr(r,c): 
        Sr=p*energy(c)-n**(2*r); R=Sr/((p-1)*dfact(2*r-1)*sig2**r); return n*(1-R)
    print(f"  n={n:3d}: c_2={cr(2,c2):.3f} c_3={cr(3,c3):.3f} c_4={cr(4,c4):.3f} c_5={cr(5,c5):.3f}")
print("  predict:  c_2=1.000 c_3=3.000 c_4=6.000 c_5=10.000")
