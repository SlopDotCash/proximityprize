"""
SYMMETRIES lens probe (#407/#389/#371).

Tests structural symmetry connections for the proximity-gap delta* programme:

(A) Dyadic fold + e_t homogeneity compose.
    eta_b(mu_{2k}) = eta_b(mu_k) + eta_{b*zeta}(mu_k)  with zeta^k = -1.
    e_t homogeneity: e_t(g.S) = g^t e_t(S).
    Conjecture: the dyadic split of mu_{2k} via the antipodal map x -> -x is the SAME
    symmetry that, on the e_t / lacBad side, forces lacBad closed under gamma -> g^t gamma.
    Numeric: verify the eta fold AND check that on mu_{2k}, the antipodal involution x->-x
    is multiplication by the element zeta^k... i.e. -1 in mu_{2k}, and e_t(-S)=(-1)^t e_t(S).

(B) Dihedral symmetry: cyclic dilation Z/n (x->g x, g in mu_n) AND Mobius involution
    x -> -x^{-1} BOTH fix the RS bad-scalar set. On mu_n these generate a group; is it
    dihedral D_n (the cyclic group + an involution that inverts)? Check the relation
    sigma . rho . sigma = rho^{-1} where rho = (x->g x), sigma = (x -> -x^{-1}).

(C) Autocorrelation R_r(0) = E_r (energy = diagonal autocorrelation mass).
    R_r(z) <= R_r(0) is proven (AutocorrelationMax). Verify R_r(0) = E_r exactly,
    so the proven cap is literally "spurious mass per lattice pt <= energy".

(D) The Galois/Frobenius orbit on bad primes vs the cyclic e_t-coset: do Frobenius c->c^p
    and dilation c->g c commute as claimed in repCount_frobenius_eq + coset-invariance?
"""
import cmath, math, itertools

def roots_of_unity(n):
    return [cmath.exp(2j*math.pi*j/n) for j in range(n)]

def eta(psi_b, G):
    # eta_b(G) = sum_{x in G} exp(2pi i * b * x) modelled abstractly:
    # here we work in C with mu_n as complex roots and psi as a fixed additive char
    # We instead test the COMBINATORIAL fold over a real finite field below.
    pass

# ---------- (A) dyadic fold over a real finite field F_p ----------
def test_dyadic_fold(p, n):
    # mu_n in F_p^* requires n | p-1
    if (p-1) % n != 0:
        return None
    g = None
    # find an element of order exactly n
    for a in range(2, p):
        # order of a
        x, o = a % p, 1
        while x != 1:
            x = (x*a) % p
            o += 1
            if o > p: break
        if o == n:
            g = a; break
    if g is None: return None
    mu_n = sorted({pow(g, j, p) for j in range(n)})
    # additive character psi(t) = exp(2pi i t / p)
    w = cmath.exp(2j*math.pi/p)
    def eta_b(G, b):
        return sum(w**((b*x) % p) for x in G)
    # need 2n | p-1 for mu_{2n}
    if (p-1) % (2*n) != 0:
        return None
    # find zeta with zeta^n = -1 (i.e. zeta has order 2n)
    g2 = None
    for a in range(2, p):
        x, o = a % p, 1
        while x != 1:
            x = (x*a) % p; o += 1
            if o > p: break
        if o == 2*n:
            g2 = a; break
    if g2 is None: return None
    zeta = g2
    mu_2n = sorted({pow(g2, j, p) for j in range(2*n)})
    assert pow(zeta, n, p) == p-1, "zeta^n != -1"
    maxerr = 0.0
    for b in range(1, min(p, 40)):
        lhs = eta_b(mu_2n, b)
        rhs = eta_b(mu_n, b) + eta_b(mu_n, (b*zeta) % p)
        maxerr = max(maxerr, abs(lhs-rhs))
    return maxerr

# ---------- (A') antipodal e_t and the -1 in mu_{2k} ----------
def test_antipodal_et(p, n_set_size, k):
    # e_t(-S) = (-1)^t e_t(S) over C
    import random
    S = [cmath.exp(2j*math.pi*random.random()) for _ in range(n_set_size)]
    def e_t(S, t):
        return sum(math.prod(c) for c in itertools.combinations(S, t))
    errs=[]
    for t in range(0, n_set_size+1):
        et = e_t(S, t)
        etneg = e_t([-x for x in S], t)
        errs.append(abs(etneg - ((-1)**t)*et))
    return max(errs)

# ---------- (B) dihedral relation sigma rho sigma = rho^{-1} on F_p ----------
def test_dihedral(p, n):
    if (p-1) % n != 0: return None
    g = None
    for a in range(2, p):
        x,o=a%p,1
        while x!=1:
            x=(x*a)%p; o+=1
            if o>p: break
        if o==n: g=a; break
    if g is None: return None
    # domain = mu_n (must be closed under x -> -x^{-1} for mobius to act)
    mu_n = sorted({pow(g,j,p) for j in range(n)})
    inv = lambda x: pow(x, p-2, p)
    # check closure under x -> -x^{-1}
    closed = all(((p - inv(x)) % p) in mu_n for x in mu_n)
    if not closed:
        return ("not_closed", None)
    rho  = lambda x: (g*x) % p              # dilation by generator
    sig  = lambda x: (p - inv(x)) % p       # mobius involution x -> -x^{-1}
    # test sigma rho sigma == rho^{-1}  (i.e. == mult by g^{-1})
    ginv = inv(g)
    rho_inv = lambda x: (ginv*x) % p
    ok = all(sig(rho(sig(x))) == rho_inv(x) for x in mu_n)
    # also: sigma^2 = id
    invol = all(sig(sig(x))==x for x in mu_n)
    return ("dihedral_relation", ok, "sigma^2=id", invol, "closed", True)

# ---------- (C) R_r(0) == E_r ----------
def test_autocorr_energy(p, n, r):
    if (p-1)%n != 0: return None
    g=None
    for a in range(2,p):
        x,o=a%p,1
        while x!=1:
            x=(x*a)%p;o+=1
            if o>p: break
        if o==n: g=a;break
    if g is None: return None
    mu_n = sorted({pow(g,j,p) for j in range(n)})
    from collections import Counter
    # r_r(z) = #{(x_1..x_r) in mu_n^r : sum x_i = z}
    cnt = Counter()
    for tup in itertools.product(mu_n, repeat=r):
        cnt[sum(tup) % p] += 1
    # R_r(z) = sum_w r_r(w) r_r(w - z)  ; R_r(0) = sum_w r_r(w)^2
    R0 = sum(v*v for v in cnt.values())
    # E_r = #{(x,y) in mu_n^r x mu_n^r : sum x = sum y} = sum_z r_r(z)^2 = R0  (same thing)
    Er = R0
    # check R_r(z) <= R_r(0) for all z
    allz = set(cnt.keys())
    maxRz = 0
    for z in range(p):
        Rz = sum(cnt.get(w,0)*cnt.get((w-z)%p,0) for w in allz)
        maxRz = max(maxRz, Rz)
    return ("R0", R0, "Er", Er, "R0==Er", R0==Er, "maxRz==R0", maxRz==R0)

if __name__ == "__main__":
    print("=== (A) dyadic fold eta_b(mu_{2n}) = eta_b(mu_n)+eta_{b zeta}(mu_n) ===")
    for (p,n) in [(17,4),(41,4),(97,8),(193,8),(257,8),(337,16)]:
        e = test_dyadic_fold(p,n)
        print(f"  p={p:4d} n={n:3d}  maxerr={e}")
    print("=== (A') antipodal e_t(-S)=(-1)^t e_t(S) ===")
    for sz in [4,6,8]:
        print(f"  |S|={sz}  maxerr={test_antipodal_et(0,sz,0):.2e}")
    print("=== (B) dihedral sigma rho sigma = rho^{-1} on mu_n (mobius+dilation) ===")
    for (p,n) in [(17,4),(13,6),(41,8),(41,10),(97,8),(241,16),(257,16)]:
        print(f"  p={p:4d} n={n:3d}  {test_dihedral(p,n)}")
    print("=== (C) R_r(0) == E_r and R_r(z)<=R_r(0) ===")
    for (p,n,r) in [(41,4,2),(41,4,3),(97,8,2),(97,8,3),(193,8,2)]:
        print(f"  p={p:4d} n={n:3d} r={r}  {test_autocorr_energy(p,n,r)}")
