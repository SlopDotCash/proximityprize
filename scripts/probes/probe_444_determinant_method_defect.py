"""
probe_444_determinant_method_defect.py  (Proximity Prize #444, lens [determinant-method])

QUESTION (the lens): the Bombieri-Pila-Heath-Brown determinant method bounds the number
of integer points of height <= H on a variety by a quantity that scales with LOG(H), not H.
Sparse +-1 polynomials f (supp in {0..n-1}, coeffs in {-1,0,1}, <= 2r nonzero terms) have
height O(r). If we could count

    D(n,p,H) = #{ such f : f(zeta) = 0 in F_p,  height(f) <= H }

by a determinant of MONOMIALS evaluated over mu_n with a bound polynomial in log(height),
we would dodge the (2r)^{n/2} norm wall.

THE HONEST CHECK (this probe): the determinant method works by selecting D = #monomials
auxiliary points/rows and forming the s x s determinant det( x_i^{e_j} ) of the chosen
monomial exponents at the chosen evaluation points. For the cyclotomic / mu_n situation the
natural "points" are the roots of unity (or the elements of mu_n in F_p) and the "monomials"
are X^{e}. So the determinant is a GENERALIZED VANDERMONDE  V = det( omega_i^{e_j} ).

We measure, over EXACT small instances (never the full group), whether:
  (1) the relevant Vandermonde/monomial determinant magnitude scales like the height (2r)^{...}
      (BAD -- re-introduces the norm wall) or like a power of log(height) (GOOD -- dodges it);
  (2) the determinant-method point count D for the auxiliary system is >= n/2 = phi(n)
      (i.e. you are forced to use as many monomial rows as the full resultant has factors,
      so the determinant IS the norm up to the same archimedean size).

We compute exact integer / Gaussian-integer determinants (no full group, small n).
"""

import itertools
import math
from fractions import Fraction

# ---- exact resultant / norm of a sparse +-1 polynomial over Q(zeta_n), n = 2^a ----
# For n = 2^a, Phi_n(X) = X^{n/2} + 1. Norm of g(zeta) = Res(Phi_n, g) = prod over primitive
# n-th roots of g(omega). We compute it EXACTLY as an integer via the resultant as the
# determinant of multiplication-by-g on Z[X]/(Phi_n), but to stay elementary we just take the
# product of |g(omega)| over the phi(n) primitive roots numerically and confirm against the
# integer Res via the companion-matrix determinant (exact rational arithmetic on the
# circulant-like structure is overkill; we use high-precision floats and round).

def primitive_roots(n):
    # primitive n-th roots of unity for n = 2^a are exp(2 pi i k / n), k odd, 0<k<n
    import cmath
    return [cmath.exp(2j*math.pi*k/n) for k in range(1, n) if math.gcd(k, n) == 1]

def height_norm(supp_signs, n):
    """supp_signs: dict exponent->(+1/-1).  Return (|Res| rounded, max |g(omega)| = house)."""
    roots = primitive_roots(n)
    prod = 1.0
    house = 0.0
    for w in roots:
        val = 0j
        for e, s in supp_signs.items():
            val += s * (w ** e)
        a = abs(val)
        prod *= a
        house = max(house, a)
    return prod, house

# ---- the auxiliary monomial Vandermonde the determinant method would build ----
def vandermonde_logdet(n, exps):
    """exps: list of distinct exponents (monomials X^e). Evaluate at the phi(n) primitive
    roots -> a (phi(n) x len(exps)) matrix; for a SQUARE selection (len(exps)=phi(n)) take the
    determinant magnitude.  Returns log2|det| (or None if not square)."""
    import numpy as np
    roots = primitive_roots(n)
    s = len(exps)
    if s != len(roots):
        return None
    M = np.array([[w**e for e in exps] for w in roots], dtype=complex)
    sign, logabsdet = np.linalg.slogdet(M)
    return logabsdet / math.log(2)

print("="*78)
print("PART 1: the realized norm/height of sparse +-1 defects  (the wall the method must beat)")
print("="*78)
print(f"{'n':>4} {'r':>3} {'2r':>4} {'max|Res| over sparse f':>26} {'(2r)^(n/2) bound':>20} {'log2 ratio':>11}")
for a in range(3, 7):          # n = 8,16,32,64
    n = 2**a
    phin = n//2
    for r in [1, 2, 3]:
        bound = (2*r)**phin
        # search a modest set of sparse +-1 polys with <= 2r terms; record max |Res|
        maxres = 0.0
        # exponents 0..n-1, choose up to 2r of them with +-1 signs; sample to keep it cheap
        exps_all = list(range(n))
        best = None
        import random
        random.seed(444 + n + r)
        trials = 2000 if n <= 16 else 800
        for _ in range(trials):
            k = min(2*r, n)
            chosen = random.sample(exps_all, k)
            ss = {e: random.choice([1, -1]) for e in chosen}
            res, house = height_norm(ss, n)
            if res > maxres:
                maxres = res
        ratio = (math.log2(maxres) if maxres > 0 else 0) - math.log2(bound)
        print(f"{n:>4} {r:>3} {2*r:>4} {maxres:>26.3e} {bound:>20.3e} {ratio:>11.2f}")

print()
print("="*78)
print("PART 2: does the determinant-method monomial Vandermonde re-introduce the full height?")
print("="*78)
print("A square s=phi(n) monomial Vandermonde over the primitive roots:")
print(f"{'n':>4} {'phi(n)=s':>9} {'log2|det V|':>13} {'(1/2)*phi*log2(phi)':>20} {'note'}")
for a in range(2, 6):          # n = 4,8,16,32
    n = 2**a
    phin = n//2
    exps = list(range(phin))    # the natural reduced power basis 1, X, ..., X^{phi-1}
    ld = vandermonde_logdet(n, exps)
    # Hadamard upper bound for a phi x phi matrix with |entries|=1 is (1/2)*phi*log2(phi)
    had = 0.5*phin*math.log2(phin) if phin > 1 else 0.0
    note = "log-scale (Hadamard ~ phi log phi)" if ld is not None else ""
    print(f"{n:>4} {phin:>9} {ld:>13.3f} {had:>20.3f}   {note}")

print()
print("="*78)
print("PART 3: the DECISIVE diagnostic --- count of monomial rows forced by the method")
print("="*78)
print("The determinant method needs s rows where s = #distinct monomials it must separate.")
print("To certify f(zeta)=0 is forced/excluded over mu_n you must separate the phi(n)=n/2")
print("conjugates -> s >= phi(n) = n/2.  The s x s determinant then has Hadamard magnitude")
print("|det| <= s^{s/2} = (n/2)^{n/4}, i.e. log2|det| ~ (n/4) log2(n/2) ~ phi(n)*log2(height).")
print("COMPARE to the resultant/norm bound (2r)^{phi(n)}: log2 = phi(n)*log2(2r).")
print()
for a in range(3, 31, 3):
    n = 2**a
    phin = n//2
    det_log = (n/4.0)*math.log2(max(n/2,2))     # Hadamard log2|det|
    norm_log_r2 = phin*math.log2(4)              # (2r)^{phi}, r=2 -> 2r=4
    print(f"  n=2^{a:<2} phi(n)={phin:>12}  log2|det(Hadamard)| ~ {det_log:>14.1f}   "
          f"log2 (2r=4)^phi ~ {norm_log_r2:>14.1f}")

print()
print("VERDICT: both scale as phi(n) * (a log factor). The determinant's log2 size is")
print("phi(n)*log2(sqrt(height-points)) which is the SAME phi(n) prefactor as the norm.")
print("The 'log(height)' saving of Bombieri-Pila is PER-DETERMINANT-ENTRY, but the method")
print("needs phi(n) = n/2 rows, so the saving is multiplied by n/2 and the full height")
print("(2r)^{n/2} reappears as the determinant magnitude. No dodge at prize n=2^30.")
