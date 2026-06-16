#!/usr/bin/env python3
"""
probe_407_defect_onset_exact.py  --  #407 norm-Mahler-lattice route, CORRECTED char-0.

Prior probe showed the Bessel value (2r-1)!! n^r is NOT the char-0 energy of mu_n at finite r --
it is only the asymptotic. The TRUE char-0 energy E_r^(0)(mu_n) = #{(x,y) in mu_n(C)^{2r} :
sum x_i = sum y_j over C}, which equals E_r mod p whenever p is large (no wraparound coincidences).

THE DEFECT (what the norm-lattice route must bound) is:
   defect(r) = E_r(mu_n mod p) - E_r^(0)(mu_n over C)
             = #{ extra additive coincidences that hold mod p but NOT over C }
             = #{(x,y) tuples whose coeff vector c (balanced, L1<=2r) has alpha_c != 0 in Z[zeta_n]
                 but alpha_c == 0 in F_p, i.e. alpha_c in P\{0} }.

This probe computes BOTH exactly (char-0 by complex enumeration, mod p by enumeration), finds the
FIRST depth r where defect(r) > 0, and the smallest prime exhibiting it. That r* is the depth at
which the FIRST short nonzero alpha enters the prime ideal P. We then read its norm vs (2r)^{phi(n)/2}.

Run:  python scripts/probes/probe_407_defect_onset_exact.py
"""
import sys, math, itertools
from collections import Counter
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def subgroup_mod_p(p, n):
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    return [pow(z, j, p) for j in range(n)]


def Er_char0_coeffs(n, r):
    """Char-0 energy of mu_n via EXACT integer coefficient vectors.
       A sum sum_{i} zeta^{a_i} over C, with a_i in Z/n, is determined (as algebraic number) by the
       coefficient vector v in Z^n reduced modulo the relation lattice of {zeta^0..zeta^{n-1}}.
       For n-th roots of unity the ONLY Z-relations among 1,zeta,...,zeta^{n-1} come from the minimal
       polynomial structure: 1,zeta,...,zeta^{phi(n)-1} is a Z-basis, and zeta^k for k>=phi(n) is an
       integer combo. So two coeff vectors give the same complex number iff they agree after rewriting
       in the power basis 1..zeta^{phi(n)-1} via the cyclotomic polynomial Phi_n.
       We compute the reduced vector exactly with integer arithmetic and hash it."""
    # cyclotomic polynomial Phi_n coefficients (integer), via sympy
    import sympy
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]  # ascending, monic leading at index phi_n
    assert Phi_coeffs[phi_n] == 1
    # reduction table: zeta^k for k in [0, n) expressed in power basis (length phi_n) as int vector.
    redtab = [[0] * phi_n for _ in range(n)]
    for k in range(phi_n):
        redtab[k][k] = 1
    for k in range(phi_n, n):
        # zeta^k = zeta * zeta^{k-1}; multiply previous reduced vector by zeta then reduce by Phi.
        prev = redtab[k - 1]
        shifted = [0] * (phi_n + 1)
        for i in range(phi_n):
            shifted[i + 1] += prev[i]
        # reduce degree phi_n term using Phi: zeta^{phi_n} = -sum_{i<phi_n} Phi_coeffs[i] zeta^i
        top = shifted[phi_n]
        for i in range(phi_n):
            shifted[i] -= top * Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    cnt = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * phi_n
        for t in tup:
            rk = redtab[t]
            for i in range(phi_n):
                v[i] += rk[i]
        cnt[tuple(v)] += 1
    return sum(c * c for c in cnt.values())


def Er_mod_p_enum(p, H, n, r):
    """Exact E_r mod p by enumeration (small n^r)."""
    cnt = Counter()
    for tup in itertools.product(H, repeat=r):
        cnt[sum(tup) % p] += 1
    return sum(c * c for c in cnt.values())


def smallest_prime_1mod_n_nondyadic(n, lo):
    c = ((lo + n - 1) // n) * n + 1
    while not (is_prime(c) and odd_part((c - 1) // n) > 1):
        c += n
    return c


def main():
    print("=" * 80)
    print(" #407 DEFECT ONSET (corrected char-0):  first r with E_r(mod p) > E_r^(0)(over C)")
    print("=" * 80)
    # First confirm char-0 == mod-p at prize primes, depth by depth, and find where they split.
    for n in (4, 6, 8, 10, 12, 16):
        phi_n = int(sympy_totient(n))
        print(f"\n n={n}  (phi(n)={phi_n}, deg of Z[zeta_n] = {phi_n})")
        # char-0 reference for several r
        print(f"   {'r':>3} {'E_r^(0) (charC)':>16}   [p-sweep: smallest p with defect>0]")
        for r in range(2, 7):
            if n ** r > 3_000_000:
                print(f"   {r:>3}   (n^r too large to enumerate exactly)"); break
            E0 = Er_char0_coeffs(n, r)
            # sweep primes p = 1 mod n upward; find smallest with E_r mod p != E0
            found = None
            lo = max(2 * n, 50)
            tested = 0
            p = smallest_prime_1mod_n_nondyadic(n, lo)
            while tested < 200:
                H = subgroup_mod_p(p, n)
                Er = Er_mod_p_enum(p, H, n, r)
                if Er != E0:
                    found = (p, Er); break
                p = smallest_prime_1mod_n_nondyadic(n, p)
                tested += 1
            if found:
                pp, Erp = found
                print(f"   {r:>3} {E0:>16}   defect first at p={pp} (p~2^{math.log2(pp):.1f}, "
                      f"E_r={Erp}, +{Erp - E0}); threshold (2r)^(phi/2)=2^{0.5*phi_n*math.log2(2*r):.1f}")
            else:
                print(f"   {r:>3} {E0:>16}   no defect in first 200 primes (1 mod {n}) "
                      f"up to p~2^{math.log2(p):.1f}")
    print("\nReading: the prize regime is n <= sqrt(p), i.e. p >= n^2. We want: is the smallest")
    print("defect-prime ALWAYS > n^2 at fixed r (defect=0 in prize regime up to r), or does the")
    print("defect appear at p ~ n^2 already (defect bites inside the prize window)?")


def sympy_totient(n):
    import sympy
    return sympy.totient(n)


if __name__ == "__main__":
    main()
