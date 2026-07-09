"""
probe_444_period_poly_newton.py  (lens [newton-polygon], issue #444, PROMISING variant)

The house M(n) = max_{b!=0} |Sum_{x in mu_n} e_p(b x)| = max archimedean abs value of a
Galois conjugate of the Gauss period eta = Sum_{x in mu_n} zeta_p^x.  The m=(p-1)/n
conjugates of eta are the ROOTS of the (irreducible, degree-m) PERIOD POLYNOMIAL
    Psi(T) = prod_{j} (T - eta_j)  in  Z[T].
So  M(n) = house(Psi) = max_j |eta_j|  (the largest root in C).

NEWTON-POLYGON LENS (the non-vacuous version): the agreement-poly NP at p was vacuous
(all roots units).  But the PERIOD polynomial Psi is a DIFFERENT, b-free, archimedean
object.  Two NP facts constrain its house:
  (1) Mahler measure:  Mahler(Psi) >= product of |eta_j| over the conjugates with |eta_j|>1,
      and house(Psi) <= Mahler(Psi) trivially is FALSE in general; but for the period poly
      the conjugates are EXCHANGEABLE-ish, and  house <= (Mahler)^{?}.  We instead use:
  (2) the elementary symmetric functions e_k(eta_1..eta_m) = +-coeff_{m-k}(Psi) are the
      INTEGER moments/coefficients; |coeff| <= C(m,k) house^k forces, conversely,
      house >= |coeff_{m-k}|^{1/k}.   And the SUM of squares Sum |eta_j|^2 = (power sum p_2)
      = m-th coefficient combination is an INTEGER = the additive-energy-free 2nd moment.

WHAT THIS PROBE MEASURES (the closed input candidate):
  We compute Psi(T) exactly for small (p,n) [m small], extract:
    * house = max |root|  (= the true M(n))
    * Mahler measure  prod max(1,|root|)
    * the 2-adic Newton polygon slopes of Psi (m=2^k regime: bad prime ell=2)
    * the L2-coefficient height  ||Psi||_2  and the bound  house <= 2 * ||Psi||_2^{1/m}? (test)
  KEY CONJECTURE TO TEST:  house(Psi) <= C * sqrt(n * log m)  with C=O(1), and whether the
  NP/coefficient data PRODUCES that sqrt(log m) factor (vs the trivial Parseval sqrt(n) floor
  and the BGK n^{1-o(1)} ceiling).

  We report  house / sqrt(n),  house / sqrt(n log m),  and  house / sqrt(n log2 m)  to see
  if the log factor is the right normalization (matches memory: C=B/sqrt(n ln m) plateaus ~1.33).
Exact: mu_n is always a PROPER subgroup.
"""

import sympy as sp
from sympy import isprime, primitive_root, exp, I, pi, Rational, nsimplify
import cmath
import math


def order_subgroup(p, n):
    assert (p - 1) % n == 0
    g0 = primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    s, x = set(), 1
    for _ in range(n):
        s.add(x)
        x = (x * g) % p
    return sorted(s), g0


def gauss_period_conjugates(p, n):
    """
    The m=(p-1)/n conjugates of eta = sum_{x in mu_n} zeta_p^x.
    Coset reps: eta_b = sum_{x in mu_n} zeta_p^{b x}, b ranging over coset reps of mu_n in F_p*.
    These m complex numbers are the roots of the period polynomial.  Return them numerically.
    """
    S, g0 = order_subgroup(p, n)
    m = (p - 1) // n
    # coset reps b: powers g0^0, g0^1, ..., g0^{m-1} (one per coset of mu_n = <g0^m>)
    reps = [pow(g0, j, p) for j in range(m)]
    zeta = cmath.exp(2j * math.pi / p)
    etas = []
    for b in reps:
        val = sum(zeta ** ((b * x) % p) for x in S)
        etas.append(val)
    return etas, m


def two_adic_newton_slopes(int_coeffs):
    """2-adic Newton polygon slopes of a poly given integer coeffs [a_0,...,a_d]."""
    pts = {}
    for i, a in enumerate(int_coeffs):
        if a != 0:
            v = 0
            aa = abs(int(a))
            while aa % 2 == 0:
                aa //= 2
                v += 1
            pts[i] = v
    pts = sorted(pts.items())
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            x3, y3 = pt
            if (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    return [(x2 - x1, sp.Rational(y2 - y1, x2 - x1)) for (x1, y1), (x2, y2) in zip(hull, hull[1:])]


def period_poly_int_coeffs(etas):
    """Reconstruct integer coeffs of prod (T - eta_j) by rounding (period poly is in Z[T])."""
    coeffs = [1.0 + 0j]
    for e in etas:
        new = [0j] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] += c
            new[i + 1] += -e * c
        coeffs = new
    # coeffs[k] = coeff of T^{m-k}; round to nearest int (imag should be ~0)
    int_coeffs = [round(c.real) for c in coeffs]
    err = max(abs(c.real - round(c.real)) for c in coeffs) if coeffs else 0
    imerr = max(abs(c.imag) for c in coeffs) if coeffs else 0
    return int_coeffs[::-1], err, imerr  # ascending a_0..a_m


def main():
    print("=" * 96)
    print("PERIOD-POLYNOMIAL NEWTON-POLYGON probe (#444): house, Mahler, 2-adic NP, log-factor")
    print("=" * 96)
    # need m=(p-1)/n moderate so the period poly is computable; n a 2-power, proper subgroup
    cases = [
        (97, 8), (113, 16), (193, 16), (257, 16), (241, 16),
        (337, 16), (577, 16), (193, 8), (769, 16), (1153, 32),
        (12289, 16), (12289, 32),
    ]
    print(f"{'p':>7} {'n':>4} {'m':>5} {'house':>8} {'Mahler':>9} {'h/sqrt(n)':>10} "
          f"{'h/sqr(nlnm)':>11} {'NP2 slopes (run,slope)':>26}")
    for p, n in cases:
        if not isprime(p) or (p - 1) % n != 0:
            continue
        m = (p - 1) // n
        if m > 200:
            continue
        etas, m = gauss_period_conjugates(p, n)
        house = max(abs(e) for e in etas)
        mahler = 1.0
        for e in etas:
            mahler *= max(1.0, abs(e))
        ic, err, imerr = period_poly_int_coeffs(etas)
        slopes = two_adic_newton_slopes(ic) if err < 0.3 else []
        hsn = house / math.sqrt(n)
        lnm = math.log(m) if m > 1 else 1.0
        hsnlm = house / math.sqrt(n * lnm) if lnm > 0 else float('nan')
        sl_str = " ".join(f"({r},{s})" for r, s in slopes[:4])
        flag = "" if err < 0.3 else f"  [recon_err={err:.2f}]"
        print(f"{p:>7} {n:>4} {m:>5} {house:>8.3f} {mahler:>9.2f} {hsn:>10.3f} "
              f"{hsnlm:>11.3f} {sl_str:>26}{flag}")
    print("-" * 96)
    print("Reading:")
    print(" * house = TRUE M(n) (max |Gauss period conjugate|).")
    print(" * h/sqrt(n) should EXCEED 1 (graph not Ramanujan, M>2sqrt(n) sometimes) and is the")
    print("   quantity the prize bounds by C*sqrt(log m).")
    print(" * 2-adic NP slopes of the PERIOD POLY: do they read off house?  (the lens's claim)")
    print(" * If all NP2 slopes are 0 (period poly is 2-adically a unit poly), the 2-adic")
    print("   Newton polygon is ALSO vacuous for the house -> lens fails the second check too.")


if __name__ == "__main__":
    main()
