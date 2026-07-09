#!/usr/bin/env python3
"""
C032_existence_vs_mass.py -- attack the C032 reframing claim.

C032 CLAIM: the proven r=2 Sidon brick (smallSubgroup_sidonModNeg: 4^φ(n)<p => no defect)
IS "fully-split ideal-SVP non-existence at length 4", and the GENERAL OPEN CORE (defect onset
at r ~ ln q, controlling BGK sqrt-cancellation) is "the SAME statement at house <= 2r" --
i.e. the prize is a quantitative CONTINUATION of the existing code: just push existence-
non-existence of sparse short ideal vectors from r=2 to r ~ ln q.

The test of whether the reframing is FAITHFUL or LOSES THE WALL:

  EXISTENCE object  T(r) = # distinct sparse-support defect points (>0 <=> a short ideal vector
                    of the split ideal exists).  This is what ideal-SVP non-existence governs.

  MASS object       M(r) = E_r(mu_n) - E_r^(0) = SUM over defects of the representation count
                    R_r(z).  This is the actual additive-energy / character-sum wall:
                    B = max_b |sum_{y in mu_n} psi(by)| is controlled by E_r via
                    B^{2r} <= q * E_r  (moment method).  The prize needs B <~ sqrt(n log q),
                    i.e. E_r ~ E_r^(0) (the char-0 Gaussian value (2r-1)!! n^r) up to r ~ ln q.

If the reframing were faithful, "no sparse short ideal vector exists" (T=0) would be equivalent
to "energy is clean" (M small / E_r ~ E_r^(0)).  But the wall is NOT about whether ONE short
vector exists; it is about the MASS once they DO exist.  Once (2r)^φ >= p the existence side
SATURATES (a short vector trivially exists -- ideal-SVP NON-existence is just FALSE there, by
Minkowski: the split ideal of norm p in dim φ(n) has lambda_1 ~ sqrt(φ) p^{1/φ} -> small).
So the existence framing is VACUOUSLY decided in the prize regime, while the MASS (the real
quantity) is wide open.  This probe quantifies:

  (A) Once T>0 (existence trivially yes), how does the MASS M(r) compare to the char-0 value
      E_r^(0)?  If M << E_r^(0) up to large r, the wall is about MASS not existence.
  (B) The "shortest length" claim: is minHouse of the shortest defect ~ 2r (tight, the
      connection's "length 2r"), or ~ lambda_1 ~ sqrt(phi) (Minkowski), i.e. is house<=2r the
      right box at all?
  (C) Minkowski check: lambda_1(p-ideal in Z[zeta_n]) ~ sqrt(phi(n)/(2 pi e)) * p^{1/phi(n)}.
      In the prize regime p^{1/phi} -> 1 so lambda_1 = O(sqrt(phi)) = O(sqrt n): short vectors
      ALWAYS exist => ideal-SVP non-existence is FALSE => the existence framing is decided NO,
      vacuously, leaving the mass/cancellation the only live quantity.
"""
import sys, math, itertools
from collections import defaultdict

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**9):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    g = primitive_root(p)
    return pow(g, (p - 1) // n, p)


def primitive_root_angles(n):
    D = n // 2
    cs = []
    for t in range(1, n, 2):
        row_c = [math.cos(2 * math.pi * t * k / n) for k in range(D)]
        row_s = [math.sin(2 * math.pi * t * k / n) for k in range(D)]
        cs.append((row_c, row_s))
    return cs


def house_of(dfold, ang):
    D = len(dfold)
    house = 0.0
    for (row_c, row_s) in ang:
        re = im = 0.0
        for k in range(D):
            dk = dfold[k]
            if dk:
                re += dk * row_c[k]; im += dk * row_s[k]
        house = max(house, math.hypot(re, im))
    return house


def energy_exact(p, z, n, r):
    """Return (E_r, T_distinct, mass, minHouse).
       E_r = # of balanced 2r-tuples (Sum x_i = Sum y_j mod p), the FULL additive energy.
       E_r^(0) = char-0 value = # with the SAME multiset (fold_x == fold_y) -> the antipodal/diag part.
       mass = E_r - E_r^(0) = defect representation mass.
       T_distinct = # distinct nonzero defect points z (existence object)."""
    ang = primitive_root_angles(n)
    D = n // 2
    zpow = [pow(z, k, p) for k in range(n)]
    side = defaultdict(lambda: defaultdict(int))
    for combo in itertools.combinations_with_replacement(range(n), r):
        v = 0
        fold = [0] * D
        for a in combo:
            v = (v + zpow[a]) % p
            if a < D: fold[a] += 1
            else: fold[a - D] -= 1
        side[v][tuple(fold)] += 1
    E_r = 0
    E_r0 = 0
    defect_points = {}
    for v, folds in side.items():
        items = list(folds.items())
        for (fx, cx) in items:
            for (fy, cy) in items:
                E_r += cx * cy
                if fx == fy:
                    E_r0 += cx * cy
                    continue
                dz = tuple(fx[k] - fy[k] for k in range(D))
                lead = next((x for x in dz if x != 0), 0)
                if lead < 0:
                    dz = tuple(-x for x in dz)
                defect_points[dz] = defect_points.get(dz, 0) + cx * cy
    houses = [house_of(list(dz), ang) for dz in defect_points] if defect_points else []
    return E_r, E_r0, sum(defect_points.values()), len(defect_points), (min(houses) if houses else float('nan'))


def double_factorial(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r


def main():
    print("=" * 110)
    print(" C032: EXISTENCE (ideal-SVP non-existence) vs MASS (energy/BGK wall).  Prize-regime proper subgroups.")
    print("=" * 110)
    print(" Faithful reframing would need: T=0  <=>  energy clean.  We test whether the LIVE quantity is")
    print(" T (existence, what ideal-SVP governs) or M (mass, the actual BGK character-sum wall).")
    print()
    for n in (8, 16, 32):
        D = n // 2
        phi = D  # n=2^mu: totient = n/2
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None:
                print(f" n={n} beta={beta}: no prize prime"); continue
            z = order_n_root(p, n)
            # Minkowski lambda_1 for the split prime ideal: covol = p (norm), dim = phi
            # lambda_1 <~ sqrt(phi) * (covol)^{1/phi} (Minkowski/Hermite, up to const)
            lam1_minkowski = math.sqrt(phi) * p ** (1.0 / phi)
            print(f"--- n={n} (phi={phi}) p={p}=2^{math.log2(p):.1f}; "
                  f"Minkowski lambda_1 ~ sqrt(phi)*p^(1/phi) = {lam1_minkowski:.2f}; sqrt(n)={math.sqrt(n):.2f} ---")
            print(f"    {'r':>2} | {'E_r':>14} {'E_r^(0)':>14} {'(2r-1)!!n^r':>14} | "
                  f"{'mass M':>12} {'M/E_r0':>8} | {'T(exist)':>8} {'minHouse':>8} {'2r':>3}")
            for r in range(2, 6):
                if math.comb(n + r - 1, r) > 1_200_000:
                    print(f"    {r:>2} |   (multisets {math.comb(n+r-1,r):.1e} too large)")
                    continue
                E_r, E_r0, mass, T, mh = energy_exact(p, z, n, r)
                gauss = double_factorial(2 * r - 1) * n ** r
                ratio = (mass / E_r0) if E_r0 else float('nan')
                print(f"    {r:>2} | {E_r:>14} {E_r0:>14} {gauss:>14} | "
                      f"{mass:>12} {ratio:>8.4f} | {T:>8} {mh:>8.2f} {2*r:>3}")
            print()
    print("READINGS:")
    print(" * E_r^(0) (same-multiset/char-0) should match the Gaussian (2r-1)!! n^r in the clean range.")
    print(" * mass M = E_r - E_r^(0): the defect contribution.  M/E_r0 ~ 0 <=> energy clean.")
    print(" * T(exist) > 0  <=>  a short sparse ideal vector EXISTS  <=>  ideal-SVP non-existence is FALSE.")
    print(" * Minkowski lambda_1 ~ sqrt(phi)*p^(1/phi): in prize regime p^(1/phi)->1 so lambda_1=O(sqrt n):")
    print("   SHORT ideal vectors ALWAYS exist => 'ideal-SVP non-existence at house<=2r' is decided NO")
    print("   for ALL r with 2r >~ lambda_1, VACUOUSLY -- the existence framing is dead, mass is the wall.")
    print(" * Compare minHouse to lambda_1 (~sqrt n) and to 2r: if minHouse << 2r, 'length 2r' is the wrong box.")


if __name__ == "__main__":
    main()
