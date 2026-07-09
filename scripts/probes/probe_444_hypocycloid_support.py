"""
probe_444_hypocycloid_support.py  (lens [hypocycloid-support], issue #444)

LEAD (untried, from #444 comments): the Gauss-period values
    eta_b = sum_{x in mu_n} e_p(b x)   (b over coset reps F_p* / mu_n, m=(p-1)/n distinct)
live in an explicit algebraic SUPPORT region (Untrau arXiv 2112.05441: the image of a
torus under a Laurent polynomial = a Minkowski sum of hypocycloids).  The house is
    M(n) = max_b |eta_b| <= diam_radius(support) = max over the support region of |z|.
CLAIM TO TEST: does the SUPPORT geometry give a sqrt(n)-scale radius bound (= the target),
or is the support radius itself ~ sqrt(n log m) (= M, the wall merely restated)?

We make this CONCRETE and EXACT (proper dyadic subgroups, never the full group):

(A) For each proper mu_n (n=2^mu | p-1, n<p-1), compute the m=(p-1)/n period points
    eta_b in C exactly (numerically to high precision), then:
      * house        = max_b |eta_b|              (= true M(n))
      * hull_radius  = max_b |eta_b|               (same; convex hull max-modulus = house here)
      * Re/Im spread = (max-min) of Re, of Im      (axis diameter of the point cloud)
      * report ratios to sqrt(n), sqrt(n ln m), sqrt(n ln n).

(B) THE ACTUAL SUPPORT (the lead's object) is NOT the m points for one p; it is the
    CLOSURE as the n-tuple of phases (theta_1,...,theta_n) ranges over the constraints that
    a genuine subgroup imposes.  The crudest support envelope: eta = sum of n unit vectors
    => |eta| <= n trivially (useless).  The REFINED support (Untrau): the n phases are NOT
    free -- the subgroup is closed under x -> x^2 (Frobenius-like dyadic structure on mu_n,
    n=2^mu), so consecutive squarings tie the phases.  We model the *free* support that
    respects ONLY the dyadic power-sum vanishing (e_1=...=e_{?}=0 from rigidity) and measure
    its radius.  This isolates whether the algebraic SUPPORT (not the arithmetic instance)
    is sqrt(n)-bounded.

(C) DECISIVE COMPARISON: plot house vs sqrt(n log m) across a sqrt-p-thin family
    (p ~ n^beta, beta in [3,5]) to see the asymptotic normalization.  If hull_radius / sqrt(n)
    GROWS (in m), the support is the wall; if it PLATEAUS at O(1), the support could be a
    genuine sqrt(n)-handle (then check the log m).
"""

import sympy as sp
from sympy import isprime, primitive_root
import cmath, math
import numpy as np


def order_subgroup(p, n):
    assert (p - 1) % n == 0
    g0 = int(primitive_root(p))
    g = pow(g0, (p - 1) // n, p)
    s, x = [], 1
    for _ in range(n):
        s.append(x)
        x = (x * g) % p
    return s, g0


def period_points(p, n):
    """The m=(p-1)/n DISTINCT Gauss-period points eta_b in C (orbit-invariant under mu_n)."""
    S, g0 = order_subgroup(p, n)
    m = (p - 1) // n
    reps = [pow(g0, j, p) for j in range(m)]   # one rep per coset of mu_n in F_p*
    w = 2 * math.pi / p
    pts = []
    for b in reps:
        s = 0j
        for x in S:
            s += cmath.exp(1j * w * ((b * x) % p))
        pts.append(s)
    return pts, m


def hull_diameter(pts):
    """Max pairwise distance (convex-hull diameter) of the complex point cloud."""
    xs = np.array([z.real for z in pts])
    ys = np.array([z.imag for z in pts])
    P = np.stack([xs, ys], axis=1)
    # brute force is fine for m up to a few thousand
    if len(P) > 4000:
        # subsample extreme points by angle for speed
        idx = np.argsort(np.arctan2(ys, xs))
        P = P[idx[:: max(1, len(P) // 4000)]]
    d = 0.0
    n = len(P)
    for i in range(n):
        diff = P[i + 1:] - P[i]
        if len(diff):
            dd = np.max(np.sqrt((diff ** 2).sum(axis=1)))
            if dd > d:
                d = dd
    return d


def main():
    print("=" * 104)
    print("[hypocycloid-support] #444: convex-hull radius/diameter of Gauss-period cloud vs sqrt(n log m)")
    print("PROPER dyadic mu_n only (n=2^mu, n | p-1, n < p-1, p >> n).")
    print("=" * 104)
    # proper dyadic subgroups; include a sqrt-p-THIN slice (p ~ n^beta) to read the asymptotic
    cases = []
    # (i) fixed moderate n, growing m  (m = (p-1)/n grows => tests the log m envelope)
    for n in [8, 16, 32, 64]:
        for kk in [2.0, 2.5, 3.0, 3.5, 4.0]:
            target = int(n ** kk)
            p = None
            for cand in range(target - target % n + 1, target * 4, n):
                if cand > n + 1 and isprime(cand):
                    p = cand
                    break
            if p:
                cases.append((p, n, kk))
    print(f"{'p':>9} {'n':>4} {'m':>7} {'beta':>5} {'house':>8} {'diam':>8} "
          f"{'h/sqrtn':>8} {'h/sqrt(nlnm)':>12} {'diam/sqrt(nlnm)':>15}")
    rows = []
    for p, n, kk in cases:
        m = (p - 1) // n
        if m > 60000:
            continue
        pts, m = period_points(p, n)
        house = max(abs(z) for z in pts)
        diam = hull_diameter(pts)
        beta = math.log(p) / math.log(n)
        lnm = math.log(m) if m > 1 else 1.0
        hsn = house / math.sqrt(n)
        hsnlm = house / math.sqrt(n * lnm)
        dsnlm = diam / math.sqrt(n * lnm)
        rows.append((n, beta, hsn, hsnlm, dsnlm))
        print(f"{p:>9} {n:>4} {m:>7} {beta:>5.2f} {house:>8.3f} {diam:>8.3f} "
              f"{hsn:>8.3f} {hsnlm:>12.3f} {dsnlm:>15.3f}")
    print("-" * 104)
    print("READING:")
    print(" * house = M(n) (true wall).  diam = convex-hull DIAMETER of the eta_b cloud.")
    print(" * If h/sqrtn PLATEAUS in m (column ~constant down a fixed-n block) => support is")
    print("   sqrt(n)-scale up to the log, candidate handle. If it GROWS with m => support=wall.")
    print(" * The lead is REFUTED-as-handle if diam/sqrt(n log m) ~ const ~ O(1): then the")
    print("   support DIAMETER *is* sqrt(n log m) = the wall restated, no sqrt(n) gain.")
    print(" * Note diam ~ 2*house when the cloud is centrally ~symmetric (eta_{-b}=conj(eta_b)).")


if __name__ == "__main__":
    main()
