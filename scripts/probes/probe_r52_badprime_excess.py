import numpy as np, math
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
cases=[(16,41521),(16,37201),(16,33713),(32,2082918049%10**6 if False else 5857)]  # n32 big primes too slow for bincount at 2e9; use smaller bad ones
# find some moderate bad primes for n=32 from the probe list: use 5857? that was beta 2.5 general. Instead test a mid-size n=32 bad prime; recompute small bad primes:
for n,p in [(16,41521),(16,37201),(16,14401),(16,11489)]:
    e=E3(p,n); e0=char0(n); w=6*n**3
    print(f"n={n} p={p} (β={math.log(p)/math.log(n):.2f}): E3={e} excess={e-e0} excess/n³={(e-e0)/n**3:.4f} E3/Wick={(e)/w:.3f}")
