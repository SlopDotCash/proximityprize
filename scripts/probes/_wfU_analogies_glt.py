# Cross-domain analogy probe: E_r(mu_n) = Gauss-period 2r-th moment
#                            = Fermat-hypersurface point count (GLT)
#                            = char-0 Gaussian/Bessel moment
import itertools, cmath, math

def gauss_periods(p, n):
    """eta_b = sum_{y in mu_n} psi(b*y), psi(x)=exp(2pi i x/p), b=0..p-1.
       mu_n = the order-n multiplicative subgroup of F_p* (n | p-1)."""
    assert (p-1) % n == 0
    g = primitive_root(p)
    sub = sorted({pow(g, ((p-1)//n)*k, p) for k in range(n)})
    assert len(sub)==n
    etas=[]
    for b in range(p):
        s=sum(cmath.exp(2j*math.pi*(b*y % p)/p) for y in sub)
        etas.append(s)
    return etas, sub

def primitive_root(p):
    if p==2: return 1
    phi=p-1
    fac=set()
    m=phi
    d=2
    while d*d<=m:
        while m%d==0:
            fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac):
            return g
    raise RuntimeError

def Er_energy(sub, p, r):
    """Additive energy / deep moment E_r = #{(a_1..a_r,b_1..b_r) in mu_n^{2r} :
       sum a_i = sum b_j  (mod p)}  = (1/p) sum_b eta_b^{?}... 
       Direct combinatorial: #{2r-tuples: a1+..+ar - b1-..-br = 0 mod p}."""
    from collections import Counter
    # distribution of r-fold sums
    c=Counter()
    for tup in itertools.product(sub, repeat=r):
        c[sum(tup)%p]+=1
    return sum(v*v for v in c.values())

def moment_from_periods(etas, p, r):
    """(1/p) sum_b |eta_b|^{2r}  should equal E_r."""
    return sum(abs(e)**(2*r) for e in etas)/p

# GLT / Fermat-hypersurface point count: #{x_1^m+...+x_{2r}^m = 0 mod p}, m=(p-1)/n
def fermat_count(p, m, vars):
    """#{(x_1..x_vars) in F_p^vars : sum x_i^m = 0}. x_i range over ALL of F_p."""
    powmap=[pow(x,m,p) for x in range(p)]
    from collections import Counter
    # build distribution of single x^m
    single=Counter(powmap)
    # convolve vars times
    dist={0:1}
    for _ in range(vars):
        nd={}
        for s,cnt in dist.items():
            for v,c2 in single.items():
                k=(s+v)%p
                nd[k]=nd.get(k,0)+cnt*c2
        dist=nd
    return dist.get(0,0)

print(f"{'p':>5}{'n':>4}{'r':>3} | {'E_r(combinat)':>14} {'(1/p)S|eta|^2r':>16} {'match':>6}")
for p,n in [(17,4),(17,8),(257,8),(97,4),(73,8),(257,16)]:
    if (p-1)%n: continue
    etas,sub=gauss_periods(p,n)
    for r in [2,3]:
        Er=Er_energy(sub,p,r)
        Mr=moment_from_periods(etas,p,r)
        ok = abs(Er-Mr)<1e-4
        print(f"{p:>5}{n:>4}{r:>3} | {Er:>14d} {Mr:>16.4f} {str(ok):>6}")
