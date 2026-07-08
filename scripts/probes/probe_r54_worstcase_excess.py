import numpy as np, math
from sympy import isprime
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
    mun=np.empty(n,dtype=np.int64); x=1
    for i in range(n): mun[i]=x; x=x*gm%p
    s2=(mun[:,None]+mun[None,:]).ravel()%p
    r2=np.bincount(s2,minlength=p)
    r3=np.zeros(p,dtype=np.int64)
    for y in mun: r3+=np.roll(r2,int(y))
    return int(np.dot(r3,r3))
char0=lambda n: 15*n**3-45*n**2+40*n
# WORST CASE: scan EVERY prime p ≡ 1 mod n in (n, LIMIT], compute excess, track max C=excess/n²
for n in (8,16,32):
    c0=char0(n); worst_C=0; worst_p=0; headroom=45*n**2-40*n; n_bad=0
    LIMIT = 200000 if n<=16 else 400000  # covers small primes where excess is largest
    p=n+1
    while p<=LIMIT:
        if (p-1)%n==0 and isprime(p):
            e=E3(p,n); exc=e-c0
            if exc!=0:
                n_bad+=1
                C=exc/n**2
                if C>worst_C: worst_C=C; worst_p=p
        p+=1
    print(f"n={n}: scanned primes≡1 mod n up to {LIMIT}: {n_bad} bad, WORST C=excess/n²={worst_C:.3f} at p={worst_p} (β={math.log(worst_p)/math.log(n):.2f} if worst_p else 0); headroom C_max=45−40/n={45-40/n:.2f}; MARGIN={45-40/n-worst_C:.2f}")
