import math
from sympy import isprime, nextprime
def factor(x):
    fs,d=set(),2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in factor(p-1)): return g
def E3(p,n):
    g=prim_root(p); gm=pow(g,(p-1)//n,p)
    mun=[]; x=1
    for _ in range(n): mun.append(x); x=x*gm%p
    # E3 = sum over s of r3(s)^2 where r3 = #representations as y1+y2+y3
    from collections import Counter
    r2=Counter()
    for y1 in mun:
        for y2 in mun:
            r2[(y1+y2)%p]+=1
    r3=Counter()
    for s2,c in r2.items():
        for y3 in mun:
            r3[(s2+y3)%p]+=c
    return sum(c*c for c in r3.values())
def bigprime(n,minv):
    P=nextprime(max(minv, 10**6))
    while (P-1)%n!=0: P=nextprime(P)
    return P
for n in (8,16,32):
    P=bigprime(n, 7**(n//2))
    e0=E3(P,n)
    wick=6*n**3
    print(f"n={n}: char-0 E3 = {e0}  (Wick 6n³ = {wick}, ratio {e0/wick:.3f})  [aux P={P}]")
    for beta in (2.5,3.0,4.0,5.0):
        p=nextprime(int(n**beta))
        while (p-1)%n!=0: p=nextprime(p)
        e=E3(p,n)
        print(f"   p={p:>9} beta={math.log(p)/math.log(n):.2f}: E3={e}  wraparound excess={e-e0}  excess/Wick={(e-e0)/wick:.4f}")
