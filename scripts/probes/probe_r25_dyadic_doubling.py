"""#466 novel exploration: dyadic square-root doubling structure for M(mu_n).
Self-contained (no sympy). Tests candidate structural bounds on
D_k = M(mu_{2^k}) = max_{b!=0} |sum_{x in mu_{2^k}} e_p(bx)|."""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d, r = n-1, 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def prime_2adic(mu):
    m = 1 << mu; t = 1
    while True:
        p = m*t+1
        if is_prime(p): return p
        t += 1

def primitive_root(p):
    # factor p-1
    n = p-1; fac=set(); d=n; f=2
    while f*f<=d:
        while d%f==0: fac.add(f); d//=f
        f+=1
    if d>1: fac.add(d)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def subgroup(p, order):
    g = primitive_root(p); h = pow(g,(p-1)//order,p)
    S=[]; x=1
    for _ in range(order): S.append(x); x=x*h%p
    return S

def Mval(p,S):
    best=0.0
    for b in range(1,p):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        best=max(best,abs(s))
    return best

for mu in range(1,9):
    p = prime_2adic(mu)
    if p > 200003: break
    Ds=[]
    for k in range(1,mu+1):
        Ds.append(Mval(p, subgroup(p,1<<k)))
    print(f"mu={mu} p={p}")
    for k in range(1,mu+1):
        n=1<<k; D=Ds[k-1]; c=D/math.sqrt(n)
        line=f"  k={k} n={n:5d} D={D:8.3f} D/sqrt(n)={c:.3f}"
        if k>=2:
            step=D-Ds[k-2]; bnd=math.sqrt(1<<(k-1))
            line+=f"  C1 step={step:7.3f}<=sqrt(2^{k-1})={bnd:6.3f}? {'OK' if step<=bnd+1e-9 else 'FAIL'}"
        line+=f"  C2 D<=sqrt(2n)? {'OK' if D<=math.sqrt(2*n)+1e-9 else 'FAIL'}"
        print(line)
