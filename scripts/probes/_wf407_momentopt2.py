import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def period_values(p,n):
    g=primitive_root(p); d=(p-1)//n; h=pow(g,d,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    m=(p-1)//n; w=2*math.pi/p
    period=[]; rep=1
    for i in range(m):
        s=0j
        for x in S: s+=cmath.exp(1j*w*((rep*x)%p))
        period.append(s); rep=(rep*g)%p
    return period,m
def primes_1modN(n, start):
    cand=start|1
    while True:
        if (cand-1)%n==0 and sympy.isprime(cand): return cand
        cand+=2

print("=== CORRECT moment method over b!=0 (the m cosets): B^{2r} <= V_{2r} = sum_s |eta_s|^{2r} ===")
print("(the b=0 spike eta_0=n is DROPPED -- it is the only obstruction in the full-sum version)")
for n in (8,16,32,64,128):
    p=primes_1modN(n, 2*n*400)
    period,m=period_values(p,n)
    absv=[abs(z) for z in period]
    B=max(absv)
    rmax=30
    V={r:sum(a**(2*r) for a in absv) for r in range(1,rmax+1)}
    bounds=[(r, V[r]**(1.0/(2*r))) for r in range(1,rmax+1)]
    rbest,best=min(bounds,key=lambda t:t[1])
    print(f"n={n:3d} p={p} m={m}: trueB={B:.4f}  bestCosetMomentBound={best:.4f} at r={rbest}  bnd/B={best/B:.3f}  bnd/sqrt(nlnm)={best/math.sqrt(n*math.log(m)):.3f}")
