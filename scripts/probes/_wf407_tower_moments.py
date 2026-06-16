import cmath, math, sympy

def primitive_root(p): return int(sympy.primitive_root(p))
def subgroup(p,n):
    g=primitive_root(p); d=(p-1)//n; h=pow(g,d,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S,g
def period_values(p,n):
    S,g=subgroup(p,n); m=(p-1)//n; w=2*math.pi/p
    period=[]; rep=1
    for i in range(m):
        s=0j
        for x in S: s+=cmath.exp(1j*w*((rep*x)%p))
        period.append(s); rep=(rep*g)%p
    return period,m
def stats(p,n,rs=(2,4,6,8,10,12)):
    period,m=period_values(p,n)
    absv=[abs(z) for z in period]
    V={r:sum(a**r for a in absv) for r in rs}
    B=max(absv)
    return B,V,m

def primes_1modN(n, count, start=None):
    out=[]; cand=(start or (n+1))
    if cand%2==0: cand+=1
    while len(out)<count:
        if (cand-1)%n==0 and sympy.isprime(cand): out.append(cand)
        cand+=1
    return out

def dfact(k):  # (2r-1)!!
    r=1
    for j in range(1,k+1,2): r*=j
    return r

# E_r(mu_n) = V_{2r}/m  (normalized 2r-fold energy per coset);  random-like = (2r-1)!! n^r
print("=== Higher fixed-k moments: E_r := V_{2r}/m  vs  (2r-1)!!*n^r (Gaussian) ===")
print("ratio = E_r / ((2r-1)!! n^r); >1 means heavier-than-Gaussian tail")
for n in (8,16,32):
    # use a LARGE m so we are deep in fixed-k regime (p >> n)
    p=primes_1modN(n,1, start=2*n*400)[0]
    B,V,m=stats(p,n)
    print(f"n={n} p={p} m={m}  B={B:.4f}  B/sqrt(n ln m)={B/math.sqrt(n*math.log(m)):.4f}")
    for r in (2,3,4,5,6):
        Er=V[2*r]/m
        gauss=dfact(2*r-1)*n**r
        # moment-method bound B <= (q E_r)^{1/2r}; q = p, but per-coset: sum_{b!=0}|eta|^{2r}=n V_{2r}
        # B^{2r} <= sum_{b}|eta_b|^{2r} = n^{2r} + n*V_{2r}; dominant n*V_{2r}=n*m*Er
        Mbound = (n**(2*r) + n*V[2*r])**(1.0/(2*r))
        print(f"   r={r}: E_r={Er:12.2f}  (2r-1)!!n^r={gauss:12.2f}  ratio={Er/gauss:7.4f}  momentB=(sum)^(1/2r)={Mbound:8.4f}")
