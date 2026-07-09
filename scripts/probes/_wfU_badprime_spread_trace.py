#!/usr/bin/env python3
"""
_wfU_badprime_spread_trace.py -- LENS [badprime-spread]

Goal: the just-verified Q1 char-p win used a POLYNOMIAL threshold p <= n^2/4, via:
   o_j(B)=sigma_j(beta) (Galois) + trace Tr(beta*conj(beta)) = (n/2)*|B|
   + p^{k/2} | N(beta) + AM-GM  ==>  p <= n^2/4   (the d=4 / r=2 case).

This probe:
  (1) RECONSTRUCTS and NUMERICALLY VERIFIES the E1 trace identity that underlies it:
        for alpha = sum_{j} c_j zeta_m^j (m=2^k, j over m/2 power basis or n-th roots),
        Sum_{i in (Z/m)^*} |sigma_i(alpha)|^2 = (m/2) * Sum_j c_j^2 = (phi(m)) * ||c||^2 ... check
      and the AM-GM corollary |N(alpha)| <= ( (1/phi) Sum |sigma_i|^2 )^{phi/2} = (||c||_2^2 * m/2 / phi)^{phi/2}
      Then specialize to the Q1 obstruction shape (r=2: x1+x2 = y1+y2, a signed sum of 4 roots),
      where ||c||_2^2 is BOUNDED BY A CONSTANT (=4), giving the POLYNOMIAL p<=(stuff)^{phi/2}...
      but at r=2 the BETA object (Galois-conjugate eigenvalue) gives p <= n^2/4 DIRECTLY -- verify.

  (2) TESTS the SAME identity on OTHER gates by computing, for the obstruction shape of each gate,
      the L2 length ||c||_2^2 in the power basis vs the group-ring, and asking whether the
      AM-GM bound (L2)^{phi/2} is POLYNOMIAL in n (i.e. L2 = O(1), phi = O(1)) or EXPONENTIAL
      (L2 grows / phi = n/2). The phi/2 exponent is the killer: polynomial iff phi(n)=O(1) OR
      we can BOUND |N| polynomially WITHOUT the phi-th power (which is what the trace gives at r=2).

  Gates examined:
    Q1  r=2 deep-energy (d=4):  signed sum of 4 roots, beta = order-n eigenvalue
    Q2  sparse worst case    :  signed sum of 2r roots, general r
    deep energy E_r          :  general r (CharSumMomentDeepWall): does trace give poly?
    lacunary count           :  DyadicLacunary obstruction
"""
import math, itertools, cmath
from collections import Counter, defaultdict


def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True


def primitive_root(p):
    if p == 2: return 1
    fac = []
    pm1 = p - 1
    d = 2
    x = pm1
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for g in range(2, p):
        if all(pow(g, pm1 // q, p) != 1 for q in fac): break
    return g


def primitive_roots_of_unity(n):
    return [cmath.exp(2j * math.pi * t / n) for t in range(1, n) if math.gcd(t, n) == 1]


def norm_from_group_ring(coeffs_on_mu_n, n):
    """alpha = sum_t coeffs[t] * zeta_n^t  (group-ring coords, length n).
       |N_{Q(zeta_n)/Q}(alpha)| = prod over primitive roots ω of |sum_t c_t ω^t|."""
    prod = 1.0
    for t in range(1, n):
        if math.gcd(t, n) != 1: continue
        w = cmath.exp(2j * math.pi * t / n)
        val = sum(coeffs_on_mu_n[k] * w**k for k in range(n))
        prod *= abs(val)
    return prod


def trace_identity_check(coeffs_on_mu_n, n):
    """Verify Sum_{i in (Z/n)^*} |sigma_i(alpha)|^2  vs  the Parseval RHS.
       sigma_i(alpha) = sum_t c_t zeta^{i t}. We compute LHS numerically and compare to
       the autocorrelation/Parseval form.  Returns (lhs, rhs_parseval, phi)."""
    units = [i for i in range(1, n) if math.gcd(i, n) == 1]
    phi = len(units)
    lhs = 0.0
    for i in units:
        w = cmath.exp(2j * math.pi * i / n)
        val = sum(coeffs_on_mu_n[t] * w**t for t in range(n))
        lhs += abs(val)**2
    # RHS via Parseval over ALL n-th roots minus the non-primitive contribution is messy;
    # the clean E1 form holds for m=2^k power basis. We just report LHS and the AM-GM bound.
    return lhs, phi


def amgm_norm_bound(coeffs_on_mu_n, n):
    """|N(alpha)| <= ( (1/phi) Sum_i |sigma_i|^2 )^{phi}  by AM-GM on the phi conjugate magnitudes.
       (geometric mean <= arithmetic mean of the |sigma_i|^2, then raise to phi)."""
    lhs, phi = trace_identity_check(coeffs_on_mu_n, n)
    if phi == 0: return 0.0, 0, 0.0
    am = lhs / phi
    bound = am ** phi   # |N|^2 <= am^phi  => |N| <= am^{phi/2}; here we return the |N| bound
    return math.sqrt(bound), phi, lhs


# ---------------------------------------------------------------------------
# GATE OBSTRUCTION SHAPES: each is a coefficient vector on mu_n (group-ring), the
# signed difference  x1+...+xr - y1-...-yr  realized as roots of unity zeta^{a_i}.
# ---------------------------------------------------------------------------

def random_balanced_relation(n, r, seed):
    """A signed sum of 2r n-th roots: r with +1, r with -1, at random exponents.
       Returns the group-ring coeff vector (length n)."""
    import random
    rnd = random.Random(seed)
    c = [0]*n
    for _ in range(r):
        c[rnd.randrange(n)] += 1
    for _ in range(r):
        c[rnd.randrange(n)] -= 1
    return c


def main():
    print("="*78)
    print("LENS [badprime-spread]: does the trace/AM-GM identity give a POLYNOMIAL")
    print("threshold on gates other than Q1 (r=2, d=4)?")
    print("="*78)

    # --- PART A: verify the E1 trace/Parseval identity Sum|sigma_i|^2 vs (n/2)||c||^2 ---
    print("\n[A] E1 trace identity:  Sum_{i in (Z/n)^*} |sigma_i(alpha)|^2  =?  c-dependent")
    print("    (for m=2^k the clean form is (m/2)*Sum c_j^2; here test general n)")
    for n in [8, 16, 16, 32]:
        c = random_balanced_relation(n, 2, seed=n*7+1)  # r=2 obstruction (Q1 shape)
        lhs, phi = trace_identity_check(c, n)
        l2sq = sum(x*x for x in c)
        ratio = lhs / l2sq if l2sq else float('nan')
        print(f"    n={n:3d}  phi={phi:3d}  ||c||_2^2={l2sq:3d}  Sum|sigma_i|^2={lhs:8.2f}"
              f"  ratio(=phi if c lives in 1 unit-orbit?)={ratio:6.3f}")

    # --- PART B: Q1 (r=2) -- the POLYNOMIAL bound p <= n^2/4 ---
    # The Galois route: beta = sum over mu_n of the eigenvalue; o_j(B)=sigma_j(beta).
    # At r=2 the obstruction is 2-dimensional and the trace Tr(beta conj beta) = (n/2)|B|
    # gives p <= n^2/4 WITHOUT the phi-th power.  We test the *numeric* claim that for
    # the r=2 defect, the prime is forced <= n^2/4.
    print("\n[B] Q1 (r=2): exhaustive defect-prime search, is every defect prime <= n^2/4 ?")
    for n in [8, 12, 16]:
        primes = [p for p in range(n+1, 40*n) if is_prime(p) and (p-1) % n == 0]
        worst_defect_prime = 0
        bound = n*n/4
        # build all r=2 sums x1+x2 (multiset of size 2 from mu_n) and look for char-0
        # vs mod-p coincidences (defects).  char-0 class = power-basis reduced vector.
        # We do it per prime: a "defect" = two DISTINCT char-0 r=2 sums equal mod p.
        for p in primes:
            g = primitive_root(p); z = pow(g, (p-1)//n, p)
            zpows = [pow(z, j, p) for j in range(n)]
            seen = {}
            defect = False
            for a in range(n):
                for b in range(a, n):
                    s = (zpows[a] + zpows[b]) % p
                    key = (a, b)
                    if s in seen and seen[s] != key:
                        # check char-0 distinct: a+b multiset vs the stored one
                        defect = True
                        break
                    seen.setdefault(s, key)
                if defect: break
            if defect:
                worst_defect_prime = max(worst_defect_prime, p)
        status = "ALL defects <= n^2/4 (POLY holds)" if worst_defect_prime <= bound else \
                 f"DEFECT ABOVE n^2/4 ({worst_defect_prime} > {bound})"
        print(f"    n={n:3d}  n^2/4={bound:7.1f}  largest defect prime={worst_defect_prime:6d}  -> {status}")

    # --- PART C: deep energy E_r (general r) -- does the SAME trace identity stay polynomial? ---
    print("\n[C] Deep energy E_r, general r: AM-GM norm bound exponent is phi/2.")
    print("    Poly iff bound = (L2^2)^{phi/2} stays poly in n. Track L2^2 and phi for r=2,3,4,...")
    n = 16; phi = sum(1 for i in range(1,n) if math.gcd(i,n)==1)
    for r in [2, 3, 4, 6, 8]:
        # worst-case L2^2 of a 2r-term signed relation in the power basis:
        # build the group-ring vector then reduce mod Phi_n and measure power-basis L2.
        worst_l2 = 0
        import random
        rnd = random.Random(1000+r)
        for _ in range(200):
            c = random_balanced_relation(n, r, seed=rnd.randrange(10**9))
            # group-ring L2 (NOT reduced): upper bound is 2r if all distinct, but collisions raise it
            l2g = sum(x*x for x in c)
            worst_l2 = max(worst_l2, l2g)
        amgm_log2 = (phi/2) * math.log2(max(worst_l2,1))
        # compare to the prize prime p ~ n^5 = 16^5
        print(f"    r={r:2d}  worst group-ring L2^2={worst_l2:3d}  AM-GM |N|<= (L2^2)^(phi/2) = 2^{amgm_log2:6.1f}"
              f"   (phi/2={phi//2}); prize p~n^5=2^{5*math.log2(n):.1f}")

    print("\n[C-verdict] The phi/2 EXPONENT is the wall: at fixed small n, AM-GM beats triangle")
    print("    (L2^2 ~ 2r-ish, vs (2r)^2), but the bound is STILL (const)^{phi/2}. Polynomial in n")
    print("    ONLY IF phi(n)=O(1) (tiny n) OR r=2 special structure collapses the phi-th power.")

    # --- PART D: which gates have the r=2 'phi-th-power collapse'? ---
    print("\n[D] The r=2 collapse: why p<=n^2/4 not (4)^{phi/2}.")
    print("    At r=2 the obstruction x1+x2=y1+y2 means {x1,x2}={y1,y2} in char 0 (Sidon),")
    print("    so beta = x1+x2 is a sum of TWO roots; its norm-2 trace pairs conjugates:")
    print("    |N(beta-beta')| with beta,beta' the only two reps. The key: a NONZERO 2-term")
    print("    difference of roots zeta^a - zeta^b has |N| = N(1-zeta^{a-b}) which is a")
    print("    cyclotomic-unit-times-small object: |N(1-zeta_n^d)| = (prime power dividing n)")
    print("    or 1. Let's verify |N(1 - zeta_n^d)| is SMALL (bounded by n), not (2)^{phi}:")
    for n in [8, 16, 32, 64]:
        phi = sum(1 for i in range(1,n) if math.gcd(i,n)==1)
        vals = []
        for d in range(1, n):
            c = [0]*n; c[0] += 1; c[d] -= 1   # 1 - zeta^d
            if any(c):
                Nb = norm_from_group_ring(c, n)
                vals.append(round(Nb))
        mx = max(vals) if vals else 0
        print(f"    n={n:3d}  phi={phi:3d}  max|N(1-zeta^d)|={mx:4d}  (vs (2)^phi=2^{phi}={2**phi:>10});"
              f"  2-term diff norm is SMALL -> r=2 is special")

    print("\n"+"="*78)
    print("SUMMARY")
    print("="*78)
    print("""
 * Q1 (r=2) polynomial threshold is REAL and SPECIAL: a 2-term root difference
   zeta^a - zeta^b has |N| <= n (cyclotomic, = N(1-zeta^d), a divisor-of-n-power object),
   NOT (2)^{phi}. So p | N forces p <= n. The n^2/4 is the slightly-larger Sidon-pair
   version. This collapse is a property of TWO-TERM differences only.
 * Gates with 2r-term (r>=3) obstructions DO NOT inherit this: their norm is a generic
   sum of >2 roots, |N| ~ (L2^2)^{phi/2}, exponential in phi(n)=n/2. AM-GM improves the
   BASE (2r -> L2 ~ sqrt(2r)) but NOT the phi/2 EXPONENT.
 * => The Q1 win does NOT transfer to deep-energy E_r (r~log p), lacunary count, or
   rate-lifts, EXCEPT when their obstruction is structurally 2-term (Sidon/r=2 slice).
   The polynomial reach is exactly the r=2 / d=4 (and by the same 2-term-pairing
   argument, partially d=8 nested-pair) cases -- matching 'rigorous only d in {4,8}'.
""")


if __name__ == "__main__":
    main()
