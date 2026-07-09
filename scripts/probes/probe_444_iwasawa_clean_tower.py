import cmath, math
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
def mu_n(p,n):
    g=primitive_root(p); m=(p-1)//n; h=pow(g,m,p)
    return [pow(h,j,p) for j in range(n)]
def house(p,n):
    sub=mu_n(p,n)
    # precompute roots
    W=[cmath.exp(2j*math.pi*k/p) for k in range(p)]
    best=0.0
    for b in range(1,p):
        s=0+0j
        for x in sub: s+=W[(b*x)%p]
        v=abs(s)
        if v>best: best=v
    return best
print("=== Clean tower: ratio M(2n)^2/M(n)^2; conjecture needs <=3 at EVERY level ===")
for p in [186113, 786433]:
    print(f"\np={p}")
    prev=None
    for mu in range(3,8):
        n=2**mu
        if (p-1)%n!=0: continue
        Mn=house(p,n)
        r=(Mn**2)/(prev**2) if prev else float('nan')
        flag='' if (math.isnan(r) or r<=3+1e-9) else '  <-- VIOLATES <=3'
        print(f" n={n:>4} M(n)={Mn:>9.4f} M^2/n={Mn**2/n:>7.3f} ratio={r:>8.4f}{flag}")
        prev=Mn
