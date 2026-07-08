"""#466 crux measurement: is the DC-subtracted spectrum {|eta_b|: b!=0} Gaussian at ALL depths?
R_r := S_r / [ (p-1) * (2r-1)!! * sigma^{2r} ],  sigma^2 = mean_{b!=0}|eta_b|^2.
Gaussian (Wick) => R_r -> 1. Growth of R_r = the obstruction. This is the exact object the
prize's moment route must bound uniformly up to r ~ ln q."""
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
def dfact(m):  # (2r-1)!!
    r=1.0
    while m>0: r*=m; m-=2
    return r
for k in (3,4,5):
    n=1<<k; lo=int(n**4); p=prime_ge_2adic(lo,n)
    if p>1_200_000: continue
    S=subgroup(p,n)
    mags=[]
    for b in range(1,p):
        z=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        mags.append(z.real*z.real+z.imag*z.imag)
    sig2=sum(mags)/len(mags)
    print(f"n={n} p={p} sigma^2={sig2:.3f} (n={n}) ln q={math.log(p*n):.1f}")
    row=[]
    for r in range(1,14):
        Sr=sum(m**r for m in mags)
        clean=(p-1)*dfact(2*r-1)*sig2**r
        row.append(f"R_{r}={Sr/clean:.2f}")
    print("   "+" ".join(row))
