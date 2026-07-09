import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def subgroup_periods(p,n):
    g=primitive_root(p); d=(p-1)//n; h=pow(g,d,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    m=(p-1)//n; w=2*math.pi/p
    period=[]; rep=1
    for i in range(m):
        s=0j
        for x in S: s+=cmath.exp(1j*w*((rep*x)%p))
        period.append(s); rep=(rep*g)%p
    return period
def primes_1modN(n, start):
    cand=start|1
    while True:
        if (cand-1)%n==0 and sympy.isprime(cand): return cand
        cand+=2

# (A) Self-similar tower: FIX p, vary n=2^a UP the dyadic tower mu_2<mu_4<...<mu_{2^a}.
#     Does B(mu_{2^a}) grow like sqrt(a) (i.e. sqrt(log n)) per the conjecture sqrt(n log m)?
#     Here m=(p-1)/n shrinks as n grows (p fixed), so log m = log p - log n.
print("=== (A) Dyadic tower at FIXED p: B(mu_{2^a}) vs a=log2(n) ===")
# pick p with large 2-adic valuation of p-1
for p in [40961, 65537, 786433, 12289, 0]:
    if p==0: break
    if not sympy.isprime(p): continue
    v2=sympy.multiplicity(2,p-1)
    print(f"p={p}, v2(p-1)={v2}")
    print(f"   {'a':>3} {'n=2^a':>7} {'m':>8} {'B':>9} {'sqrt(n)':>9} {'B/sqrt(n)':>10} {'sqrt(n ln m)':>12} {'B/sqrt(nlnm)':>12}")
    for a in range(1, min(v2, 12)+1):
        n=2**a
        if (p-1)%n: continue
        per=subgroup_periods(p,n)
        B=max(abs(z) for z in per); m=(p-1)//n
        lnm=math.log(m) if m>1 else 1
        print(f"   {a:>3} {n:>7} {m:>8} {B:>9.4f} {math.sqrt(n):>9.4f} {B/math.sqrt(n):>10.4f} {math.sqrt(n*lnm):>12.4f} {B/math.sqrt(n*lnm):>12.4f}")
