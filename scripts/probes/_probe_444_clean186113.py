import cmath, math, numpy as np
def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def primitive_root(p):
    fact=list(factorize(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fact): return g
def house(p,n):
    g=primitive_root(p); m=(p-1)//n; h=pow(g,m,p)
    sub=np.array([pow(h,j,p) for j in range(n)],dtype=np.int64)
    W=np.exp(2j*np.pi*np.arange(p)/p)
    best=0.0
    for b in range(1,p):
        idx=(b*sub)%p
        v=abs(W[idx].sum())
        if v>best: best=v
    return best
p=186113
print(f"p={p}, p-1 factor {factorize(p-1)}")
prev=None
for mu in range(3,8):
    n=2**mu
    if (p-1)%n!=0: continue
    Mn=house(p,n)
    r=(Mn**2)/(prev**2) if prev else float('nan')
    flag='' if (math.isnan(r) or r<=3+1e-9) else '  <-- VIOLATES <=3'
    print(f" n={n:>4} M(n)={Mn:>9.4f} ratio={r:>8.4f}{flag}")
    prev=Mn
