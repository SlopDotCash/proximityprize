import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def gen_order_n(p,n):
    g=primitive_root(p); d=(p-1)//n; return pow(g,d,p), g
def subgroup_set(p,n):
    h,_=gen_order_n(p,n); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S
def eta(p,S,b):
    w=2*math.pi/p; return sum(cmath.exp(1j*w*((b*x)%p)) for x in S)

# DUPLICATION / FOLDING identity test:
# mu_{2n} = mu_n  union  zeta*mu_n  where zeta is a 2n-th root with zeta^n=-1 (zeta = sqrt of mu_n gen)
# So eta_b(mu_{2n}) = eta_b(mu_n) + eta_{b*zeta}(mu_n)?  NO: x in zeta*mu_n => b*x = (b*zeta)*y, y in mu_n
# => eta_b(mu_{2n}) = eta_b(mu_n) + eta_{b zeta}(mu_n).  zeta = element of mu_{2n} not in mu_n with zeta^2 in mu_n.
print("=== Folding identity: eta_b(mu_{2n}) = eta_b(mu_n) + eta_{b*zeta}(mu_n) ===")
for p in [12289, 40961]:
    for n in [8,16,32]:
        if (p-1)%(2*n): continue
        Sn=subgroup_set(p,n); S2n=subgroup_set(p,2*n)
        h2n,_=gen_order_n(p,2*n)
        zeta=h2n  # primitive 2n-th root => zeta*mu_n is the other coset, zeta^n=-1
        # verify zeta^n = -1 mod p
        assert pow(zeta,n,p)==p-1, (pow(zeta,n,p),p-1)
        maxerr=0
        for b in range(1,40):
            lhs=eta(p,S2n,b)
            rhs=eta(p,Sn,b)+eta(p,Sn,(b*zeta)%p)
            maxerr=max(maxerr,abs(lhs-rhs))
        print(f"p={p} n={n}->2n={2*n}: max|lhs-rhs| over b=1..39 = {maxerr:.2e}  (zeta^n=-1: OK)")
