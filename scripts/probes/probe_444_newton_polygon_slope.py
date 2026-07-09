"""
probe_444_newton_polygon_slope.py  (lens [newton-polygon], issue #444)

QUESTION (the honesty check the prompt flags):
  Agreement of codeword g (deg<k) with worst word w = x^a + x^{a-1} over mu_n subset F_p*
  = #{x in mu_n : g(x)=w(x)} = #(mu_n-roots of h := g - w).
  Does the p-ADIC NEWTON POLYGON of a global lift of h constrain that root count?

THE OBSTRUCTION TO TEST:
  Every x in mu_n is a p-adic UNIT (|x|_p = 1, v_p(x)=0).  A p-adic root r of a polynomial
  over Q_p has v_p(r) = -slope of a Newton-polygon segment.  Unit roots <=> slope-0 segment.
  So ALL mu_n-roots sit on the SINGLE slope-0 (horizontal) segment of NP_p(h-lift).
  The Newton polygon at p therefore gives ONLY:
     (# mu_n-roots) <= (length of the slope-0 segment) = (# slope-0 roots, w/ mult).
  KEY TEST: is that slope-0 length << deg h (so a nontrivial bound), or is it ~ deg h
  (so vacuous, all roots are units, NP_p says nothing)?

MORE PROMISING VARIANT (b-sensitive, the real proposal):
  Pick a DIFFERENT prime ell (an auxiliary modulus, ell != p) and stratify the roots of the
  *integer* polynomial H(x) = numerator of g(x)-w(x) when g has small-height integer coeffs.
  But over F_p the agreement is an F_p-eval; the only intrinsic valuation is at p.
  => the lens MUST use the p-adic NP, and the test below decides if it is vacuous.

We compute, for the genuinely worst structured words and the lift h(x)=x^a+x^{a-1}-c (the
SHAPE of the agreement poly when g is constant, the cleanest nondegenerate case), the
slope-0 segment length of NP_p, vs deg, vs the actual #(mu_n-roots).
Exact arithmetic, proper subgroup mu_n (never the full group).
"""

import sympy as sp
from sympy import isprime, primitive_root


def order_subgroup_gen(p, n):
    """A generator g of the order-n subgroup mu_n of F_p* (requires n | p-1)."""
    assert (p - 1) % n == 0
    g0 = primitive_root(p)
    return pow(g0, (p - 1) // n, p)


def mu_n(p, n):
    g = order_subgroup_gen(p, n)
    s, x = [], 1
    for _ in range(n):
        s.append(x)
        x = (x * g) % p
    return s


def newton_polygon_p_slopes(coeffs_padic_val, p):
    """
    coeffs_padic_val: dict i -> v_p(a_i) for nonzero a_i of poly sum a_i x^i.
    Returns list of (run_length, slope) for the lower convex hull (Newton polygon).
    slope of a segment from (i1,v1) to (i2,v2) is (v2-v1)/(i2-i1); horizontal run = #roots
    of that slope (= -slope p-adic valuation of those roots).
    """
    pts = sorted(coeffs_padic_val.items())
    # lower convex hull
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            x3, y3 = pt
            # cross product; keep lower hull (turn must be counter-clockwise -> pop)
            if (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) <= 0:
                hull.pop()
            else:
                break
        hull.append(pt)
    segs = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        slope = sp.Rational(y2 - y1, x2 - x1)
        segs.append((x2 - x1, slope))
    return segs


def vp(n_int, p):
    if n_int == 0:
        return sp.oo
    k = 0
    n_int = abs(int(n_int))
    while n_int % p == 0:
        n_int //= p
        k += 1
    return k


def analyze(p, n, a, c_int):
    """
    Agreement poly shape h(x) = x^a + x^{a-1} - c  (g = constant c, worst word x^a+x^{a-1}).
    Lift coefficients to Z: a_a=1, a_{a-1}=1, a_0=-c.  All p-adic vals of unit coeffs are 0;
    -c may be divisible by p.  Compute NP_p slope-0 length vs actual mu_n root count.
    """
    pts = {a: 0, a - 1: 0}
    if c_int % p != 0:
        pts[0] = vp(-c_int if (-c_int) != 0 else 1, p) if c_int != 0 else sp.oo
        pts[0] = 0  # c a unit
    else:
        pts[0] = vp(c_int, p)
    segs = newton_polygon_p_slopes(pts, p)
    slope0_len = sum(run for run, s in segs if s == 0)
    # actual mu_n roots of h mod p
    S = mu_n(p, n)
    cmod = c_int % p
    roots = sum(1 for x in S if (pow(x, a, p) + pow(x, a - 1, p) - cmod) % p == 0)
    return slope0_len, a, roots, segs


def main():
    print("=" * 78)
    print("NEWTON-POLYGON LENS probe (#444): is NP_p slope-0 length a nontrivial root bound?")
    print("=" * 78)
    cases = [
        (97, 8), (193, 16), (257, 16), (769, 16), (1153, 32),
        (12289, 16), (12289, 32), (12289, 64), (40961, 64),
    ]
    print(f"{'p':>7} {'n':>4} {'a':>4} {'deg':>4} {'slope0_len':>11} {'mu_n_roots':>11} "
          f"{'bound_tight?':>13}")
    worst_ratio = 0.0
    for p, n in cases:
        if not isprime(p) or (p - 1) % n != 0:
            continue
        # worst structured word degree a near n-1 (consecutive monomials), constant g
        for a in (n - 1, n // 2 + 1, n // 4 + 1):
            if a < 2:
                continue
            best_roots = 0
            best = None
            # sweep c over a few unit values; pick the one maximizing mu_n agreement
            for c in range(1, min(p, 60)):
                slope0_len, deg, roots, segs = analyze(p, n, a, c)
                if roots > best_roots:
                    best_roots = roots
                    best = (slope0_len, deg, roots, segs)
            slope0_len, deg, roots, segs = best
            ratio = slope0_len / deg if deg else 0
            worst_ratio = max(worst_ratio, ratio)
            tight = "VACUOUS" if slope0_len >= deg else f"<deg by {deg - slope0_len}"
            print(f"{p:>7} {n:>4} {a:>4} {deg:>4} {slope0_len:>11} {roots:>11} {tight:>13}")
    print("-" * 78)
    print(f"worst slope0_len/deg ratio = {worst_ratio:.3f}")
    print()
    print("VERDICT on the honesty check:")
    print("  If slope0_len == deg for the structured worst words (ratio 1.0), the p-adic")
    print("  Newton polygon is VACUOUS for mu_n-root counting: every root is a unit, the")
    print("  whole polygon is one horizontal segment, NP gives only '#roots <= deg'.")
    print("  A NONtrivial NP bound requires the constant/low-order coeffs to carry p-adic")
    print("  valuation (a slope), which the agreement poly g(x)-w(x) over a UNIT domain")
    print("  does NOT generically have.")


if __name__ == "__main__":
    main()
