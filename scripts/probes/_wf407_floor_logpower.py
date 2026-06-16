import cmath, math
# Compute B(mu_n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x),
# and test which law fits: sqrt(n*log m)  vs  sqrt(n)*log m  vs  2*sqrt(n).
# Prize-diagonal: pick prime p = 1 mod n with m=(p-1)/n; sweep n=2^k, keep m moderate-but-growing.
def find_prime(n, mlow):
    # smallest prime p>=n*mlow+1 with p-1 divisible by n
    import sympy
    m = mlow
    while True:
        p = n*m+1
        if sympy.isprime(p):
            return p, m
        m += 1

try:
    import sympy
except ImportError:
    print("no sympy"); raise SystemExit

def order_n_elt(p, n):
    # generator of mu_n: g = primitive_root^((p-1)/n)
    g = sympy.primitive_root(p)
    return pow(g, (p-1)//n, p)

print(f"{'n':>6} {'p':>14} {'m':>10} {'B':>9} {'sqrt(n)':>9} {'B/sqrt(nlogm)':>14} {'B/(sqrtn*lnm)':>14} {'B/(2sqrtn)':>11}")
import random
for k in [4,5,6,7,8,9,10]:
    n = 2**k
    # choose m to grow modestly so log m has range; keep p not astronomically large
    p, m = find_prime(n, 50*k)        # m ~ 50k.. so log2 m grows
    h = order_n_elt(p, n)
    H = [pow(h, j, p) for j in range(n)]
    # eta_b constant on cosets: only need one b per coset, but just sweep b=1..min(p-1, big) representative set.
    # Use full sweep over a coset-rep set: pick m representatives = one per coset. Cheaper: sweep b over all of 1..p-1 is too big.
    # Instead sweep b over m coset reps: reps = {g^i : i=0..m-1} where g=prim root (covers all cosets).
    g = sympy.primitive_root(p)
    reps = [pow(g, i, p) for i in range(m)] if m <= 4000 else [random.randrange(1,p) for _ in range(4000)]
    twopi_over_p = 2*math.pi/p
    B = 0.0
    for b in reps:
        s = 0+0j
        for x in H:
            ang = twopi_over_p * ((b*x) % p)
            s += cmath.exp(1j*ang)
        a = abs(s)
        if a > B: B = a
    lnm = math.log(m)
    sn = math.sqrt(n)
    print(f"{n:>6} {p:>14} {m:>10} {B:>9.3f} {sn:>9.3f} {B/math.sqrt(n*lnm):>14.4f} {B/(sn*lnm):>14.4f} {B/(2*sn):>11.4f}")
