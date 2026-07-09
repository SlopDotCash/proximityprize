"""
Probe for connection C069 (issue #407):
  "The TWO cocycles coincide: the additive tower factor a^{2^k}-b^{2^k}=prod(a^{2^j}+b^{2^j})
   IS the Galois norm N(alpha)=prod_w g(w) bounding the char-p energy defect."

Two objects:
  (TOWER)  T(a,b) = a^{2^k} - b^{2^k} = (a-b) * PROD_{j<k} (a^{2^j} + b^{2^j})
           -- k = mu factors, factors are DIFFERENT exponents 2^j at FIXED (a,b)=(1+w, c).
           identity over any commutative ring; here we instantiate over F_p (prize regime).
  (NORM)   N(g) = Res(Phi_n, g) = PROD_{w prim n-th root of 1} g(w)
           -- phi(n) = n/2 factors, SAME signed-monomial g at DIFFERENT embeddings w.

Claim under test (C069): these are the SAME multiplicative cocycle; the tower (mu factors)
is the 2-adic refinement of the norm (n/2 factors), grouping phi(n) embeddings into mu
tower levels of sizes 2^j.

PRIZE REGIME: n = 2^mu a PROPER subgroup of F_p*, p prime = 1 mod n, p ~ n^beta, beta in [4,5].

We test, at proper-subgroup primes for n = 16, 32, 64:
  (A) STRUCTURAL: do the two products have the same number of factors and the same factor
      structure? (mu vs n/2 -- they differ unless n/2 = mu, i.e. n=2,4. So for prize n
      they CANNOT be the same product term-by-term.)
  (B) NUMERICAL: can the tower factorization of a SINGLE collision (1+w)^n = c^n be made to
      equal / regroup the norm N(g) of the additive-energy relation? Is there ANY g and
      single (w,c) for which prod over tower levels = prod over embeddings (up to units)?
  (C) The honest interpretation: the tower object lives in F_p (a single residue), the norm
      object lives in Z (an integer whose p-divisibility is the defect criterion). Test
      whether the tower factor product, lifted to Z via the cyclotomic integer, reproduces N.
"""

import sympy as sp
from sympy import primerange, isprime, totient, cyclotomic_poly, Symbol, prod
import math

# ---------- find prize-regime proper-subgroup primes p = 1 mod n, p ~ n^beta ----------
def find_prize_primes(n, beta_lo=4, beta_hi=5, want=2):
    lo = int(n**beta_lo)
    hi = int(n**beta_hi)
    out = []
    p = lo - (lo % n) + 1
    if p < lo:
        p += n
    while p <= hi and len(out) < want:
        if isprime(p):
            out.append(p)
        p += n
    return out

def primitive_root_mod_p(p):
    # smallest primitive root mod p
    phi = p - 1
    factors = sp.factorint(phi).keys()
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no prim root")

def order_n_element(p, n):
    # an element of exact order n in F_p* (n | p-1)
    assert (p - 1) % n == 0
    g = primitive_root_mod_p(p)
    z = pow(g, (p - 1) // n, p)
    # sanity
    assert pow(z, n, p) == 1 and all(pow(z, d, p) != 1 for d in range(1, n))
    return z

# ===================================================================================
# (A) STRUCTURAL: count factors in each product.
# ===================================================================================
def structural_compare(mu_list):
    print("=" * 78)
    print("(A) STRUCTURAL factor-count comparison")
    print(f"{'mu':>4} {'n=2^mu':>8} {'tower #factors (mu)':>20} {'norm #factors phi(n)=n/2':>26}")
    rows = []
    for mu in mu_list:
        n = 2**mu
        tower_factors = mu           # k = mu factors a^{2^j}+b^{2^j}, j=0..mu-1
        norm_factors = totient(n)    # phi(2^mu) = 2^{mu-1} = n/2
        rows.append((mu, n, tower_factors, int(norm_factors)))
        print(f"{mu:>4} {n:>8} {tower_factors:>20} {int(norm_factors):>26}")
    return rows

# ===================================================================================
# (B/C) Try to realize the claimed "same cocycle". The norm N(g)=Res(Phi_n,g) is an
# integer attached to a FIXED relation polynomial g (signed sum of 2r roots of unity).
# The tower product is attached to a SINGLE pair (1+w, c) and factors the integer
# (1+w)^n - c^n (over Z if we lift). Test whether the tower product, as an integer,
# is a NORM of the SAME shape, and whether its factor count matches.
# ===================================================================================
def tower_vs_norm_integer(mu_list):
    print("=" * 78)
    print("(B/C) Integer-level test: is the tower product the cyclotomic norm of the")
    print("      SAME signed-monomial g?  Compare factor counts & the actual integers.")
    X = Symbol('X')
    for mu in mu_list:
        n = 2**mu
        k = mu
        # A genuine additive-energy relation g for mu_n: a signed sum of 2r roots of unity.
        # Take the SIMPLEST nonzero shape that is the curve object: g(X) = (1+X)^? -- but
        # the norm threshold uses g = signed monomial. The tower's pair is (a,b)=(1+w,c).
        # The honest "relation" object whose collision the tower factors is
        #   h_{w,c}(X) := (1+X)^n - c^n  evaluated at X=w in F_p  (a curve collision),
        # NOT a fixed signed-monomial in Z. So at the integer level the natural norm is
        #   N := Res(Phi_n, g) for g = the 2r-term relation.
        # The two simply attach to DIFFERENT polynomials.  Demonstrate the mismatch:
        #   tower:  a^n - b^n factors into k=mu binomials a^{2^j}+b^{2^j}  (a,b free vars).
        #   norm:   Res(Phi_n, g) = prod over phi(n)=n/2 embeddings of ONE g.
        # Show the tower binomial a^{2^j}+b^{2^j} is NOT cyclotomic-norm-shaped:
        # its "embedding product" form would need a SINGLE-variable g, but it is bivariate.
        # Concretely set b=1 (specialize c=1, the principal collision) to get a univariate
        # comparison the claim would need:  a^n - 1 = prod_{d|n} Phi_d(a)  (true, n/... factors)
        # vs the tower  a^n-1 = (a-1) prod_{j<k}(a^{2^j}+1).
        a = Symbol('a')
        tower_form = (a - 1) * prod([(a**(2**j) + 1) for j in range(k)])
        cyclo_form = prod([cyclotomic_poly(d, a) for d in sp.divisors(n)])
        diff = sp.expand(tower_form - cyclo_form)
        # both equal a^n - 1
        an_minus_1 = sp.expand(a**n - 1)
        print(f"\n  mu={mu}, n={n}:")
        print(f"    tower factorization of a^n-1 : {k} non-trivial binomial factors "
              f"a^(2^j)+1, j=0..{k-1}  (+ (a-1))")
        print(f"    cyclotomic factorization     : {len(sp.divisors(n))} factors Phi_d(a), d|n; "
              f"PRIMITIVE one Phi_n has degree phi(n)={int(totient(n))}")
        print(f"    tower_form == a^n-1 ? {sp.expand(tower_form)==an_minus_1};  "
              f"cyclo_form == a^n-1 ? {cyclo_form==an_minus_1 or sp.expand(cyclo_form)==an_minus_1}")
        # KEY: tower binomial a^{2^j}+1 = Phi_{2^{j+1}}(a) EXACTLY for prime-power 2-cyclotomics!
        for j in range(k):
            tb = a**(2**j) + 1
            phi_idx = 2**(j+1)
            cp = cyclotomic_poly(phi_idx, a)
            match = sp.expand(tb - cp) == 0
            print(f"      level j={j}: a^(2^{j})+1  vs  Phi_(2^{j+1})(a)  ->  equal? {match} "
                  f"(deg {2**j} = phi(2^{j+1})={int(totient(phi_idx))})")
    print()
    print("  OBSERVATION: with c specialized to 1, the tower binomials ARE the 2-power")
    print("  cyclotomics Phi_{2^{j+1}}.  The PRIMITIVE one Phi_n=Phi_{2^mu} is the LAST")
    print("  tower factor a^{2^{mu-1}}+1 alone (degree phi(n)=n/2).  So the norm's single")
    print("  factor Phi_n is ONE tower level, NOT the whole tower product.")

# ===================================================================================
# (D) The decisive test of the CONNECTION's actual assertion:
# 'the tower gives a level-by-level handle on WHICH embeddings make N(alpha) small,
#  grouping phi(n) embeddings into mu tower levels of sizes 2^j'.
# Test: order the phi(n) primitive embeddings w of mu_n by their 2-adic tower level
#   level(w) := the j with w of 'order exactly 2^{j+1}' as a ROOT type -- but ALL
#   primitive n-th roots have order exactly n=2^mu, i.e. level j=mu-1 ONLY.
# So there is NO nontrivial grouping of the phi(n) PRIMITIVE embeddings into mu levels:
# every primitive root sits at the single top level. Verify.
# ===================================================================================
def embedding_level_grouping(mu_list):
    print("=" * 78)
    print("(D) Do the phi(n) PRIMITIVE embeddings split into mu tower levels of sizes 2^j?")
    print("    Tower level of a root zeta := j such that ord(zeta)=2^{j+1}.")
    for mu in mu_list:
        n = 2**mu
        # primitive n-th roots of unity = exp(2 pi i k/n), gcd(k,n)=1
        prim_ks = [kk for kk in range(1, n) if math.gcd(kk, n) == 1]
        # multiplicative order of zeta^k = n/gcd(k,n) = n (since gcd=1) => order n=2^mu always
        levels = {}
        for kk in prim_ks:
            ordr = n // math.gcd(kk, n)
            j = int(math.log2(ordr)) - 1   # ord = 2^{j+1}
            levels.setdefault(j, 0)
            levels[j] += 1
        print(f"  mu={mu}, n={n}: #primitive embeddings phi(n)={len(prim_ks)};  "
              f"level histogram {dict(sorted(levels.items()))}")
    print("  => ALL phi(n) primitive embeddings sit at the SINGLE top level j=mu-1.")
    print("     The 'sizes 2^j' grouping (claimed) does NOT hold for the primitive roots:")
    print("     it holds for ALL n-th roots (the FULL group), which is the #400 full-group trap.")

if __name__ == "__main__":
    mu_list = [3, 4, 5, 6]   # n = 8,16,32,64
    structural_compare(mu_list)
    print()
    # prize primes (sanity that the regime is real)
    for mu in [4, 5]:
        n = 2**mu
        ps = find_prize_primes(n, 4, 5, want=2)
        print(f"prize primes for n={n} (p=1 mod n, n^4..n^5): {ps[:2]}")
    print()
    tower_vs_norm_integer(mu_list)
    print()
    embedding_level_grouping(mu_list)
