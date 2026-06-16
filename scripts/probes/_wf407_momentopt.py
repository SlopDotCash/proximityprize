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

print("=== Moment-method optimization over r in FIXED-INDEX regime ===")
print("B^{2r} <= sum_{b in F}|eta_b|^{2r} = n^{2r}+ n*V_{2r}.  best over r vs true B.")
for n in (8,16,32,64):
    p=primes_1modN(n, 2*n*400)
    period,m=period_values(p,n)
    absv=[abs(z) for z in period]
    B=max(absv)
    rmax=18
    V={r:(n**(2*r)+ n*sum(a**(2*r) for a in absv)) for r in range(1,rmax+1)}
    bounds=[(r, V[r]**(1.0/(2*r))) for r in range(1,rmax+1)]
    rbest,best=min(bounds,key=lambda t:t[1])
    print(f"n={n:3d} p={p} m={m}: trueB={B:.4f}  bestMomentBound={best:.4f} at r={rbest}  ratio bnd/B={best/B:.3f}  sqrt(n ln m)={math.sqrt(n*math.log(m)):.3f}")
    # show the curve near the optimum
    for r in range(max(1,rbest-2), rbest+5):
        if r in V: print(f"      r={r:2d}: (n^2r+nV2r)^(1/2r)={V[r]**(1.0/(2*r)):.4f}")
