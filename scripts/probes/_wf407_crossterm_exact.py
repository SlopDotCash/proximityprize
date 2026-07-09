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
# cross sum  C = sum_{b in cosets of mu_2n} Re(eta_b(n) conj eta_{zeta b}(n)).
# Closed form derivation: Re(eta_b(n) conj eta_{zeta b}(n)) summed over ALL b in F^*
#   = Re sum_b sum_{x,y in mu_n} e_p(bx) e_p(-zeta b y) = Re sum_{x,y} sum_b e_p(b(x - zeta y))
#   over b in F^* : inner = (p-1) if x=zeta y else -1.  x=zeta y impossible (x in mu_n, zeta y in zeta mu_n disjoint)
#   so sum over ALL b!=0 = Re sum_{x,y}(-1) = -n^2.  Over cosets of mu_2n (each repeated 2n times? no...)
# Let's just measure both "all b!=0" and "one per 2n-coset".
print("=== exact cross term, two normalizations ===")
for p in [12289,40961,786433]:
    for n in [8,16,32,64]:
        if (p-1)%(2*n): continue
        Sn=subgroup_set(p,n); h2n,_=gen_order_n(p,2*n); zeta=h2n
        g=primitive_root(p)
        # all b in F^*:
        all_b=0.0
        for b in range(1,p):
            all_b += (eta(p,Sn,b)*eta(p,Sn,(zeta*b)%p).conjugate()).real
        # one per 2n-coset (m2 reps):
        m2=(p-1)//(2*n); coset=0.0; rep=1
        for i in range(m2):
            coset += (eta(p,Sn,rep)*eta(p,Sn,(zeta*rep)%p).conjugate()).real
            rep=(rep*g)%p
        print(f"p={p} n={n}: cross(all b!=0)={all_b:.2f} (pred -n^2={-n**2})  cross(per 2n-coset)={coset:.3f} (=-n/2? {-n/2})")
