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
def run(p,n):
    g=prim_root(p); m=(p-1)//n
    ind={}; x=1
    for k in range(p-1): ind[x]=k; x=x*g%p
    ks=np.array([ind[a] for a in range(1,p)])
    chi_full=np.zeros(p); chi_full[1:]=np.where(ks%2==0,1.0,-1.0)
    ts=np.arange(p); om=(1-ts)%p
    lam=lambda j,arr: np.concatenate(([0],np.exp(2j*np.pi*j*n*ks/(p-1))))[arr]
    J=np.zeros(m,dtype=complex)
    for j in range(m):
        J[j]=np.sum(lam(j,ts)*chi_full[om])
    mun=[pow(g,(p-1)//n*i,p) for i in range(n)]
    errs=[];amax=0
    for t in [1,2,5,m//3]:
        lhs=sum(J[(j+t)%m]*np.conj(J[j]) for j in range(m))
        rhs=0
        for u in mun:
            ys=np.arange(1,p)
            rhs+=np.sum(chi_full[(1-u*ys)%p]*chi_full[(1-ys)%p]*lam(t,ys))
        rhs*=m
        errs.append(abs(lhs-rhs)/max(abs(lhs),1))
        amax=max(amax,abs(lhs)/(m*(n)*math.sqrt(p)))
    print(f"p={p} n={n} m={m}: identity max rel err={max(errs):.2e}  max|A(t)|/(m·n·√q)={amax:.3f}")
for (p,n) in [(577,8),(3457,8),(4129,16),(5953,32)]:
    run(p,n)
