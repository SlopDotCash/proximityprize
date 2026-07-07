import cmath
def probe(p, n, m):
    # find primitive root
    def order(a):
        k=1; x=a%p
        while x!=1: x=x*a%p; k+=1
        return k
    g=next(a for a in range(2,p) if order(a)==p-1)
    psi=lambda a: cmath.exp(2j*cmath.pi*(a%p)/p)
    # discrete log
    dlog={}; x=1
    for k in range(p-1): dlog[x]=k; x=x*g%p
    def chi(j,a):  # chi^j where chi(g^k)=e^{2pi i k/m}
        if a%p==0: return 0
        return cmath.exp(2j*cmath.pi*j*dlog[a%p]/m)
    G=sorted({pow(g,(p-1)//n*t,p) for t in range(n)})
    H=[a for a in range(1,p) if dlog[a]%m==0]
    eta=lambda b: sum(psi(b*y) for y in G)
    T=lambda j,s0: sum(chi(j,s0-x).conjugate() for x in G)
    gs=lambda j: sum(chi(j,a)*psi(a) for a in range(p))
    D=set(G)|{0}
    worst=0
    for s0 in range(p):
        if s0 in D: continue
        lhs=m*sum(eta(b).conjugate()*psi(b*s0) for b in H)
        rhs=-n+sum(gs(j)*T(j,s0) for j in range(1,m))
        worst=max(worst,abs(lhs-rhs))
    print(f"p={p} n={n} m={m} |H|={len(H)} worst |lhs-rhs| = {worst:.2e}")
for m in (2,4,5): probe(41,8,m)
probe(73,8,3); probe(73,8,4)
