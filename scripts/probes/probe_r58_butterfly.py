import numpy as np, cmath, math
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
def periods(p,n):
    # mu_n and mu_{n/2}, psi(x)=exp(2pi i x/p)
    g=prim_root(p); gm=pow(g,(p-1)//n,p)
    mu=[pow(gm,k,p) for k in range(n)]
    zeta=gm  # primitive n-th root; generator of G, and G/H rep (zeta notin H=squares)
    H=[pow(gm,2*j,p) for j in range(n//2)]  # squares = mu_{n/2}
    w=lambda x: cmath.exp(2j*math.pi*(x%p)/p)
    def eta(S,b): return sum(w(b*y) for y in S)
    return mu,H,zeta,eta,p
for n in (8,16,32):
    p=n+1
    while not (isprime(p) and (p-1)%n==0): p+=n
    mu,H,zeta,eta,p=periods(p,n)
    # verify butterfly: eta_b(mu_n) = eta_b(H) + eta_{zeta*b}(H) for all b
    maxerr=0; cross=0
    for b in range(p):
        lhs=eta(mu,b); rhs=eta(H,b)+eta(H,zeta*b)
        maxerr=max(maxerr,abs(lhs-rhs))
        cross += eta(H,b)*eta(H,zeta*b).conjugate()
    # sup norms
    Mn=max(abs(eta(mu,b)) for b in range(1,p))
    Mm=max(abs(eta(H,b)) for b in range(1,p))
    print(f"n={n} p={p}: butterfly max|LHS-RHS|={maxerr:.2e}  Σ_b crossterm={abs(cross):.2e}")
    print(f"    M_n=sup‖η(μ_n)‖={Mn:.3f}  M_{{n/2}}={Mm:.3f}  ratio M_n/M_{{n/2}}={Mn/Mm:.3f}  (√2={math.sqrt(2):.3f}); M_n/√n={Mn/math.sqrt(n):.3f}")
