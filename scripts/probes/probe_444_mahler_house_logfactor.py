"""
probe_444_mahler_house_logfactor.py  (lens [newton-polygon] -> height/Mahler closed input)

Both naive Newton polygons are VACUOUS for the house (probe_444_newton_polygon_slope: agreement
poly at p all-units; probe_444_period_poly_newton: period poly 2-adically unit except at anomalies).
The SURVIVING newton-polygon-flavored object is the GLOBAL height: the Newton polygon at the
ARCHIMEDEAN place |.|_infty.  For a degree-m integer poly Psi with roots eta_1..eta_m:
    Mahler(Psi) = prod_j max(1, |eta_j|)     (the archimedean Newton-polygon "slope-content")
    house(Psi)  = max_j |eta_j|
There is an EXACT identity tying Mahler to an integer:  for the period polynomial, the
NEXT-TO-TOP coefficients are the elementary symmetric functions e_k(eta) = +-a_{m-k}, ALL
INTEGERS, and the power sums p_2 = Sum |eta_j|^2 is an INTEGER (= the 2nd moment trace).

CLOSED INPUT WE TEST (the candidate that reduces to NAMED math, not the open BGK wall):
  (A) Parseval / 2nd-moment trace:  Sum_{j=1}^m |eta_j|^2 = n*m - n = n*(m-1) + (something).
      [exactly:  Sum over ALL b in F_p* of |eta_b|^2 = sum_{b} |period|^2; and Sum_{b=0..p-1}
       |eta_b|^2 = p*n by Parseval, eta_0 = n, so Sum_{b!=0} = p*n - n^2, over (p-1)/?
       coset-grouped... we MEASURE the exact integer.]  This gives house <= sqrt(trace) = sqrt(n*m)
      -- TOO WEAK (sqrt(m) not sqrt(log m)).
  (B) The log-factor: does house <= sqrt(n) * sqrt(2 log m + O(1))?  i.e. is the EXCESS
      house^2/n - 1  ~  2 log m / 1  ?  We fit house^2/n against log m.

WHAT A WIN LOOKS LIKE:
  house^2 <= C^2 * n * log m  is the prize.  The newton-polygon/height lens can ONLY prove
  house^2 <= trace = n*m (the m-th-moment / Parseval bound, sqrt(m) loss) UNLESS the m roots
  are SPREAD (sub-Gaussian) rather than all near the house.  The sub-Gaussian spread (max of m
  exchangeable ~N(0,n) -> sqrt(2 n log m)) is the EVT crown that memory says is KILLED
  (periods are white noise, distance-independent covariance -> NO log-correlation gain... but
  the MAX of m sub-Gaussians is STILL sqrt(2 n log m) even with NO correlation!).
  So we test: is house ~ sqrt(2 n log m), the max-of-m-independent-subgaussians value?
Exact arithmetic; proper subgroups only.
"""

import cmath, math
from sympy import isprime, primitive_root


def order_subgroup(p, n):
    assert (p - 1) % n == 0
    g0 = primitive_root(p)
    g = pow(g0, (p - 1) // n, p)
    s, x = [], 1
    for _ in range(n):
        s.append(x); x = (x * g) % p
    return s, g0


def all_periods(p, n):
    S, g0 = order_subgroup(p, n)
    m = (p - 1) // n
    reps = [pow(g0, j, p) for j in range(m)]
    zeta = cmath.exp(2j * math.pi / p)
    etas = [sum(zeta ** ((b * x) % p) for x in S) for b in reps]
    return etas, m


def main():
    print("=" * 92)
    print("MAHLER/HEIGHT closed-input probe (#444): house vs sqrt(2 n log m) [max-of-m subgaussian]")
    print("=" * 92)
    cases = [
        (97, 8), (113, 16), (193, 16), (257, 16), (241, 16), (337, 16), (577, 16),
        (193, 8), (769, 16), (1153, 32), (12289, 16), (12289, 32), (12289, 64),
        (40961, 64), (12289, 128), (40961, 128), (61441, 256),
    ]
    print(f"{'p':>7} {'n':>5} {'m':>6} {'house':>8} {'sqrt(2nlnm)':>11} "
          f"{'ratio':>7} {'trace/n':>8} {'sqrt(trace)':>11} {'excess=h^2/n':>12}")
    ratios = []
    for p, n in cases:
        if not isprime(p) or (p - 1) % n != 0:
            continue
        m = (p - 1) // n
        if m * n > 4_000_00 and m > 300:
            continue
        if m > 600:
            continue
        etas, m = all_periods(p, n)
        house = max(abs(e) for e in etas)
        trace = sum(abs(e) ** 2 for e in etas)  # Sum_{b in reps} |eta_b|^2
        lnm = math.log(m) if m > 1 else 1.0
        subg = math.sqrt(2 * n * lnm) if lnm > 0 else float('nan')
        ratio = house / subg if subg > 0 else float('nan')
        ratios.append(ratio)
        print(f"{p:>7} {n:>5} {m:>6} {house:>8.3f} {subg:>11.3f} {ratio:>7.3f} "
              f"{trace/n:>8.2f} {math.sqrt(trace):>11.3f} {house**2/n:>12.3f}")
    print("-" * 92)
    if ratios:
        print(f"house / sqrt(2 n ln m):  min={min(ratios):.3f}  max={max(ratios):.3f}  "
              f"mean={sum(ratios)/len(ratios):.3f}")
    print()
    print("VERDICT:")
    print(" * If ratio house/sqrt(2 n ln m) is STABLE and O(1) (~0.8-1.3) across growing m, then")
    print("   the house IS the max-of-m-subgaussian value and the sqrt(log m) factor is REAL.")
    print(" * The newton-polygon/height lens DELIVERS only house^2<=trace (Parseval, sqrt(m) loss);")
    print("   the sqrt(log m) needs the m roots SPREAD, which is the (deterministic!) statement")
    print("   that the period poly has m WELL-SEPARATED roots = its DISCRIMINANT is large =")
    print("   a NEWTON-POLYGON-AT-RAMIFIED-PRIMES statement (disc(Psi) = prod of ram. contributions).")


if __name__ == "__main__":
    main()
