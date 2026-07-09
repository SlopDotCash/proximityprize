"""
wf407-w2 / thread L2-nover4 — the EXACT char-0 cyclotomic orbit count #orbits(w=4) for GENERAL n.

TARGET: confirm the closed form for n = 8,12,16,20,24,28,32 (NOT just powers of 2), watching the
3 | n vs 4 | n parity, and decide what the precise closed form is for general n.

Object (char-0, exact over Z[zeta_n] modulo the n-th cyclotomic polynomial Phi_n):
  4-element SUBSETS S = {zeta^a, zeta^b, zeta^c, zeta^d}, distinct exponents mod n, with
    e_2(S) = sum_{i<j} zeta^{exp_i+exp_j} = 0   (vanishing in Z[zeta_n])
    e_1(S) = sum of the 4 roots != 0
  counted up to the mu_n action S |-> zeta^t * S.

We compute e_1, e_2 EXACTLY by reducing the coefficient vector on {1,zeta,...,zeta^{n-1}} modulo
Phi_n (integer polynomial GCD-free reduction: a vector v in Z^n represents sum v_j zeta^j; it is 0
in Z[zeta_n] iff Phi_n(X) | (sum v_j X^j) as integer polynomials, equivalently the reduction of
the polynomial mod Phi_n is the zero polynomial). We get Phi_n via the standard divisor recursion
X^n - 1 = prod_{d|n} Phi_d.
"""

import itertools
from sympy import symbols, Poly, cyclotomic_poly, ZZ

X = symbols('X')

def phi_poly(n):
    return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def is_zero_in_cyclotomic(exps_with_sign, n, Phi):
    """exps_with_sign: list of (exponent mod n, coeff). Returns True iff sum coeff*zeta^exp = 0
       in Z[zeta_n], i.e. the polynomial sum coeff*X^{exp mod n} reduces to 0 mod Phi_n."""
    coeff = [0] * n
    for (e, c) in exps_with_sign:
        coeff[e % n] += c
    P = Poly(coeff[::-1], X, domain=ZZ)  # coeff[j] is coefficient of X^j
    # rebuild properly: Poly wants highest-degree-first list
    # Build from dict to be safe:
    P = Poly.from_dict({(j,): coeff[j] for j in range(n) if coeff[j] != 0}, gens=X, domain=ZZ)
    if P.is_zero:
        return True
    r = P.rem(Phi)
    return r.is_zero

def e2_zero(exps, n, Phi):
    terms = [((exps[i] + exps[j]) % n, 1) for i, j in itertools.combinations(range(4), 2)]
    return is_zero_in_cyclotomic(terms, n, Phi)

def e1_zero(exps, n, Phi):
    terms = [(e % n, 1) for e in exps]
    return is_zero_in_cyclotomic(terms, n, Phi)

def canonical_orbit_rep(exps, n):
    best = None
    for t in range(n):
        shifted = tuple(sorted((e + t) % n for e in exps))
        if best is None or shifted < best:
            best = shifted
    return best

def enumerate_orbits(n):
    Phi = phi_poly(n)
    orbits = set()
    e2cnt = 0
    e2_e1nz = 0
    for exps in itertools.combinations(range(n), 4):
        if not e2_zero(exps, n, Phi):
            continue
        e2cnt += 1
        if e1_zero(exps, n, Phi):
            continue
        e2_e1nz += 1
        orbits.add(canonical_orbit_rep(exps, n))
    return e2cnt, e2_e1nz, sorted(orbits)

if __name__ == "__main__":
    print(f"{'n':>4} {'fac':>10} {'#e2=0':>7} {'#e2=0,e1!=0':>12} {'#orbits':>8} "
          f"{'n/4-1':>6} {'floor(n/4)-1':>12} {'match_p2law':>11}")
    for n in [8, 12, 16, 20, 24, 28, 32]:
        e2cnt, e2_e1nz, orbits = enumerate_orbits(n)
        norb = len(orbits)
        nq = n // 4 - 1
        # factor string
        from sympy import factorint
        fac = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in factorint(n).items())
        is_p2 = (n & (n - 1) == 0)
        match = (norb == nq)
        print(f"{n:>4} {fac:>10} {e2cnt:>7} {e2_e1nz:>12} {norb:>8} {nq:>6} {nq:>12} "
              f"{str(match):>11}  p2={is_p2}")
        for rep in orbits:
            shifted = tuple(sorted((e - rep[0]) % n for e in rep))
            print(f"        rep {shifted}")
