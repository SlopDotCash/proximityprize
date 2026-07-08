"""#466 DECISIVE: does the DC-subtracted moment method recover the prize bound sqrt(n ln(p/n))?
Compute S_r = sum_{b!=0} |eta_b|^{2r} exactly (eta_b = sum_{x in mu_n} e_p(bx)).
Moment-r L-infinity bound: B_r = S_r^{1/2r} >= max_b|eta_b|. Best = min_r B_r.
Test: is min_r B_r ~ C sqrt(n ln(p/n)) with r* ~ ln q, and how tight vs true max?"""
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

for k in (3,4,5):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    if p>1_200_000: print(f"n={n} p={p} skip"); continue
    S=subgroup(p,n)
    # |eta_b|^2 for all b
    mags=[]
    for b in range(1,p):
        z=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        mags.append((z.real*z.real+z.imag*z.imag))
    truemax=math.sqrt(max(mags))
    L=math.log(p/n); target=math.sqrt(n*L)
    print(f"n={n} p={p} truemax={truemax:.3f}  sqrt(n ln(p/n))={target:.3f}  truemax/target={truemax/target:.3f}")
    best=(1e9,None)
    for r in range(1,14):
        Sr=sum(m**r for m in mags)   # sum_{b!=0}|eta_b|^{2r}
        Br=Sr**(1/(2*r))
        if Br<best[0]: best=(Br,r)
    print(f"   moment method: min_r S_r^(1/2r) = {best[0]:.3f} at r*={best[1]}  (ln q={L+math.log(n):.1f})  ratio-to-target={best[0]/target:.3f}  ratio-to-truemax={best[0]/truemax:.3f}")
