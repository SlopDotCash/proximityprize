"""
C091: Collision Plancherel = Shaw second-moment on a different group?

Claim (C091): plancherel_collision (collision*|A| = sum_psi ||T_psi||^2, T_psi = sum_{|S|=a} psi(stat S))
and shawError_second_moment (sum_{s0} ||S||^2 = |V| * sum_{psi perp s1, psi!=0} ||1hat_S(psi)||^2)
are the SAME Plancherel identity (energy = sum of squared Fourier coeffs) on two groups A and V; the
off-diagonal collision mass IS the Shaw operator's L^2 mass; both bottom out in the same partial
subgroup character sum.

We test, at PRIZE-REGIME proper-subgroup primes (dyadic mu_n proper in F_q*, q ~ n^beta, beta 4-5):
 (1) Both identities hold exactly (sanity, both are in-tree axiom-clean already).
 (2) The abstract meta-lemma:  energy(f) = sum_psi ||fhat(psi)||^2 over an arbitrary finite abelian
     group G, with fhat(psi) = sum_x f(x) psi(x). Both plancherel_collision and the Shaw 2nd moment
     are instances. We verify each is literally an instance of ONE Plancherel template, and we verify
     the meta-lemma on a generic random function on a generic abelian group.
 (3) The HEADLINE quantitative claim: is the off-diagonal collision mass  sum_{psi!=0} ||T_psi||^2
     equal to the Shaw L^2 mass  |V| * sum_{psi perp s1, psi!=0} ||1hat_S(psi)||^2 ?
     We compute BOTH at the prize subgroup with stat = subset-sum (a=2, the prize's pair object) on
     A=F_q, and the Shaw mass for S = a far coset / ball on V=F_q (1-dim word space), and compare.
 (4) Where does each bottom out: the per-character factor of T_psi (elementary symmetric in psi(x))
     vs the Shaw 1hat_S(psi) = eta_b (incomplete subgroup char sum). Are they the same partial sum?

All exact integer / Gaussian-integer-free via cmath but with integer checks where possible.
"""
import cmath, math, itertools, random

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prize_primes(n, beta_lo=4.0, beta_hi=5.2, count=2):
    """primes q = 1 mod n with q ~ n^beta, mu_n proper subgroup (n < q-1), n | q-1."""
    target_lo = int(n**beta_lo); target_hi = int(n**beta_hi)
    out = []
    q = target_lo - (target_lo % n) + 1
    if q < target_lo: q += n
    while q <= target_hi and len(out) < count:
        if is_prime(q) and (q-1) % n == 0 and (q-1)//n > 1:
            out.append(q)
        q += n
    return out

def subgroup(g_gen, n, q):
    """the order-n subgroup mu_n of F_q^*, given a generator g of order n."""
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x*g_gen) % q
    return S

def find_gen_order_n(n, q):
    """find an element of exact order n in F_q^*."""
    # take a primitive root h, raise to (q-1)/n
    for h in range(2, q):
        # check primitive root cheaply via order test on small set: just trust pow
        cand = pow(h, (q-1)//n, q)
        # verify order exactly n
        ok = True
        for d in range(1, n):
            if n % d == 0 and d < n and pow(cand, d, q) == 1:
                ok = False; break
        if ok and pow(cand, n, q) == 1 and cand != 1:
            return cand
    return None

def chi(b, x, q):
    """additive character psi_b(x) = exp(2 pi i b x / q) of F_q (as a value)."""
    return cmath.exp(2j*math.pi*((b*x) % q)/q)

# ---------------------------------------------------------------------------
# (2) META-LEMMA sanity: energy(f) = sum_psi ||fhat(psi)||^2 on a small abelian group Z_m.
# ---------------------------------------------------------------------------
def metalemma_check(m, trials=3):
    """Plancherel on Z_m: sum_x |f(x)|^2 * m == sum_psi |fhat(psi)|^2 (with fhat = sum f(x) psi(x))."""
    ok = True
    for _ in range(trials):
        f = [random.randint(-3,3) for _ in range(m)]
        lhs = sum(abs(v)**2 for v in f) * m
        rhs = 0.0
        for b in range(m):
            fhat = sum(f[x]*cmath.exp(2j*math.pi*(b*x)/m) for x in range(m))
            rhs += abs(fhat)**2
        if abs(lhs - rhs) > 1e-6*max(1,abs(lhs)):
            ok = False
    return ok

# ---------------------------------------------------------------------------
# (3a) COLLISION side: stat = subset-sum, a-element subsets of mu_n, group A = F_q.
#   collision*q = (C(n,a))^2 + sum_{b!=0} ||T_b||^2,  T_b = sum_{|S|=a} psi_b(sum S).
# ---------------------------------------------------------------------------
def collision_identity(G, a, q):
    n = len(G)
    subsets = list(itertools.combinations(G, a))
    # collision count: ordered pairs of a-subsets with equal subset-sum mod q
    from collections import Counter
    sums = Counter((sum(S) % q) for S in subsets)
    collision = sum(c*c for c in sums.values())
    Cna = len(subsets)  # C(n,a)
    # spectral: sum_b ||T_b||^2, T_b = sum_S psi_b(sum S)
    energy = 0.0
    offdiag = 0.0
    for b in range(q):
        Tb = sum(cmath.exp(2j*math.pi*((b*(sum(S) % q)) % q)/q) for S in subsets)
        e = abs(Tb)**2
        energy += e
        if b != 0:
            offdiag += e
    lhs = collision * q
    return collision, Cna, lhs, energy, offdiag

# ---------------------------------------------------------------------------
# (3b) SHAW side on V = F_q (1-dim word space n_word=1, so a "line" is all of F_q, direction s1).
#   For a 1-dim V the hyperplane psi perp s1 is trivial; use V = F_q^2 to make it nontrivial? The
#   prize word space is V = (ι -> F). To keep this a clean spectral comparison we instead directly
#   compute the Shaw L^2 mass object: |V| * sum_{psi != 0} ||1hat_S(psi)||^2 with NO hyperplane
#   restriction (the cleanest comparison to the unrestricted collision off-diagonal), for S = the
#   subgroup mu_n viewed as a subset of V = F_q. This is the "Plancherel of 1_S on V" object.
# ---------------------------------------------------------------------------
def shaw_mass_unrestricted(S_set, q):
    """ |V| * sum_{psi != 0 over F_q} ||1hat_S(psi)||^2,  1hat_S(b) = sum_{s in S} psi_b(-s). """
    V = q
    total = 0.0
    for b in range(q):
        if b == 0: continue
        ihat = sum(cmath.exp(2j*math.pi*((-b*s) % q)/q) for s in S_set)
        total += abs(ihat)**2
    return V*total

def parseval_indicator(S_set, q):
    """ full Parseval: sum_{all psi} ||1hat_S(psi)||^2 = |V|*|S| (in-tree parseval_indicator)."""
    V = q
    total = 0.0
    for b in range(q):
        ihat = sum(cmath.exp(2j*math.pi*((-b*s) % q)/q) for s in S_set)
        total += abs(ihat)**2
    return total, V*len(S_set)

# ---------------------------------------------------------------------------
# Run
# ---------------------------------------------------------------------------
print("="*78)
print("(2) META-LEMMA: Plancherel energy = sum of squared Fourier coeffs on Z_m")
for m in (7, 13, 16):
    print(f"   Z_{m}: meta-lemma holds = {metalemma_check(m)}")

print()
print("="*78)
print("PRIZE REGIME comparisons (proper dyadic mu_n, q ~ n^beta, beta in [4,5])")
for n in (8, 16):
    primes = find_prize_primes(n, count=2)
    print(f"\n n = {n}   prize primes q (mu_n proper, n|q-1, (q-1)/n>1): {primes}")
    for q in primes:
        g = find_gen_order_n(n, q)
        if g is None:
            print(f"   q={q}: no order-{n} generator found, skip"); continue
        G = subgroup(g, n, q)
        assert len(set(G)) == n, "subgroup not size n"
        assert all(pow(x, n, q) == 1 for x in G), "not in mu_n"
        # (3a) collision identity for a = 1 and a = 2
        for a in (1, 2):
            collision, Cna, lhs, energy, offdiag = collision_identity(G, a, q)
            ident_ok = abs(lhs - energy) < 1e-5*max(1, lhs)
            main = Cna*Cna
            offdiag_ok = abs((main + offdiag) - lhs) < 1e-5*max(1,lhs)
            print(f"   q={q} a={a}: collision={collision} C(n,a)={Cna}  "
                  f"collision*q={lhs}  sum_b||T_b||^2={energy:.1f} (ident={ident_ok})  "
                  f"main=(C)^2={main} offdiag={offdiag:.1f} (main+off=lhs:{offdiag_ok})")
        # (3b) Shaw L^2 mass with S = mu_n on V = F_q (unrestricted) + parseval check
        shaw_mass = shaw_mass_unrestricted(G, q)
        pars, pars_expected = parseval_indicator(G, q)
        print(f"   q={q}    Shaw-mass(unrestr, S=mu_n) = |V|*sum_{{b!=0}}||eta_b||^2 = {shaw_mass:.1f}")
        print(f"   q={q}    parseval_indicator: sum_all ||eta_b||^2 = {pars:.1f}  (=|V||S|={pars_expected})")
        # Compare: is collision off-diagonal (a=2) == Shaw mass?  (the HEADLINE)
        coll2, Cna2, lhs2, en2, off2 = collision_identity(G, 2, q)
        ratio = shaw_mass/off2 if off2 else float('inf')
        print(f"   q={q}    HEADLINE check: collision-offdiag(a=2)={off2:.1f}  vs Shaw-mass={shaw_mass:.1f}"
              f"  ratio Shaw/offdiag={ratio:.3f}  EQUAL={abs(shaw_mass-off2)<1e-5*max(1,off2)}")

print()
print("="*78)
print("(4) Per-character factor: collision T_b is ELEMENTARY-SYMMETRIC in {psi_b(x): x in mu_n};")
print("    Shaw 1hat_S(b)=eta_b is the LINEAR sum sum_{x in mu_n} psi_b(x). Same per-char input set,")
print("    different symmetric function. e_1 = eta_b; e_2 = (eta_b^2 - p_2)/2 where p_2 = eta_{2b}.")
# demonstrate the Newton link at one prime
n = 8; q = find_prize_primes(n, count=1)[0]; g = find_gen_order_n(n, q); G = subgroup(g, n, q)
for b in (1, 3, 5):
    eta_b = sum(cmath.exp(2j*math.pi*((b*x) % q)/q) for x in G)       # e_1 = eta_b
    eta_2b = sum(cmath.exp(2j*math.pi*((2*b*x) % q)/q) for x in G)    # p_2 = sum psi_{2b}(x)... = eta over 2b
    # T_b at a=2 is e_2 of {psi_b(x)} = sum over pairs psi_b(x+y) = (e_1^2 - p_2)/2
    Tb2 = sum(cmath.exp(2j*math.pi*((b*(x+y) % q)) /q*1) for x,y in itertools.combinations(G,2))
    e2_newton = (eta_b**2 - eta_2b)/2
    print(f"   q={q} b={b}: eta_b={eta_b:.3f}  T_b(a=2)={Tb2:.3f}  (e1^2-p2)/2={e2_newton:.3f}  "
          f"Newton-match={abs(Tb2-e2_newton)<1e-6}")
print("="*78)
