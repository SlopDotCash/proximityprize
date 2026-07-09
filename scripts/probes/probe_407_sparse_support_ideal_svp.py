#!/usr/bin/env python3
"""
probe_407_sparse_support_ideal_svp.py  --  #407 IDEAL-SVP-SPLIT-NEWANGLE (efficient v2).

ASSIGNED ANGLE: bound the SPARSE-SUPPORT sub-count of the fully-split cyclotomic ideal-SVP
problem below baseline, using levers GoN/well-roundedness ignore.

THREE NESTED OBJECTS (kept rigorously separate -- the whole point):
  T(r,p)  = # distinct nonzero p-defect points z in 𝔭 that are SIGNED SUMS of <=2r roots of
            unity (the PRIZE object: support sparsity in the GROUP-RING basis Z^n).
  F(r,p)  = # distinct nonzero p-defect points z in 𝔭 with ||σ(z)||_∞ <= 2r (the GoN / well-
            roundedness / box object; T ⊆ F since each sparse z has ||σ(z)||_∞ <= 2r).
  M(r,p)  = representation MASS = sum over defect z of R_r(z) = exact (E_r - E_r^(0)).

KEY QUESTIONS:
  (1) Is T strictly << F?  (does support sparsity cut the count below the box?)
  (2) Does T obey a 1/p density (T ~ |T_r|/p) or is there a STRUCTURED excess?
  (3) What is min house = min_z max_t|σ_t(z)| over sparse defects, vs the (2r)^φ norm wall and
      vs the well-rounded λ_1 ~ sqrt(n/2)?  (sparse-support short vector)
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
    """precompute cos/sin of (2π t/n)*k for t odd (primitive n-th roots), k in 0..n-1."""
    D = n // 2
    cs = []
    for t in range(1, n, 2):
        row_c = [math.cos(2 * math.pi * t * k / n) for k in range(D)]
        row_s = [math.sin(2 * math.pi * t * k / n) for k in range(D)]
        cs.append((row_c, row_s))
    return cs


def house_and_lognorm(dfold, ang):
    """house(z) = max_t |σ_t(z)|; log|N(z)| = sum_t log|σ_t(z)|, over power-fold dfold (len D)."""
    D = len(dfold)
    house = 0.0; logN = 0.0; ok = True
    for (row_c, row_s) in ang:
        re = im = 0.0
        for k in range(D):
            dk = dfold[k]
            if dk:
                re += dk * row_c[k]; im += dk * row_s[k]
        mag = math.hypot(re, im)
        house = max(house, mag)
        if mag < 1e-9:
            ok = False
        else:
            logN += math.log(mag)
    return house, (logN if ok else float('nan'))


# ---------------------------------------------------------------------------
# Sparse sumset enumeration via meet-in-the-middle on the GROUP-RING coords.
# A sparse defect: a signed multiset of <=2r roots ζ^a, i.e. group vector c in Z^n with
# ||c||_1 <= 2r, c != fold-to-0, sum c_k z^k = 0 mod p.
# We enumerate it as r positive picks (the x's) and r negative picks (the y's): the balanced
# additive-energy relation Σx = Σy.  Then z = Σx - Σy.  Meet in the middle on x vs y.
# ---------------------------------------------------------------------------

def sparse_defects(p, z, n, r, ang):
    """Enumerate all balanced relations Σ_{i<=r} ζ^{a_i} = Σ_{j<=r} ζ^{b_j} mod p (with multiplicity
       allowed, multisets), record distinct power-fold defect points (dfold != 0) and the
       representation count R_r(dfold).  Returns dict of stats."""
    D = n // 2
    zpow = [pow(z, k, p) for k in range(n)]
    # x-side: all multisets of size r from {0..n-1}, value Σ ζ^{a} mod p, and char-0 fold vector.
    # We map value -> list of (fold_tuple, multiplicity_count). Then a balanced relation is
    # x-value == y-value. Defect = fold_x != fold_y (different algebraic numbers, same mod p).
    from collections import Counter
    side = defaultdict(lambda: defaultdict(int))  # modp value -> {fold_tuple: count}
    for combo in itertools.combinations_with_replacement(range(n), r):
        v = 0
        fold = [0] * D
        for a in combo:
            v = (v + zpow[a]) % p
            if a < D: fold[a] += 1
            else: fold[a - D] -= 1
        side[v][tuple(fold)] += 1
    # Now count, for each value, pairs (fold_x, fold_y) with fold_x != fold_y -> defect z = fold_x - fold_y
    defect_points = {}   # dfold tuple (canonical) -> representation count R_r
    char0_pairs = 0
    total_pairs = 0
    for v, folds in side.items():
        items = list(folds.items())
        for (fx, cx) in items:
            for (fy, cy) in items:
                total_pairs += cx * cy
                if fx == fy:
                    char0_pairs += cx * cy
                    continue
                # defect: z = fold_x - fold_y (algebraically nonzero, == 0 mod p)
                dz = tuple(fx[k] - fy[k] for k in range(D))
                # canonicalize sign: leading nonzero positive
                lead = next((x for x in dz if x != 0), 0)
                if lead < 0:
                    dz = tuple(-x for x in dz)
                defect_points[dz] = defect_points.get(dz, 0) + cx * cy
    # stats on the distinct defect points
    houses = []; lognorms = []; linf_box = []
    for dz in defect_points:
        h, lN = house_and_lognorm(list(dz), ang)
        houses.append(h);
        if not math.isnan(lN): lognorms.append(lN)
    return {
        'T_distinct': len(defect_points),     # # distinct sparse defect POINTS (the prize object)
        'mass': sum(defect_points.values()),  # E_r - E_r^(0) contribution from these (representation mass)
        'char0_pairs': char0_pairs,
        'total_pairs': total_pairs,
        'min_house': min(houses) if houses else float('nan'),
        'max_house': max(houses) if houses else float('nan'),
        'min_lognorm': min(lognorms) if lognorms else float('nan'),
        'defect_points': defect_points,
    }


def main():
    print("=" * 100)
    print(" #407 SPARSE-SUPPORT IDEAL-SVP (split prime).  T=distinct sparse defect pts; mass=E_r-E_r^(0).")
    print("=" * 100)
    print(" Levers tested: support-sparsity count T, its 1/p density, min house vs (2r)^φ wall & λ_1~√(n/2).")
    print()
    for n in (8, 16, 32):
        D = n // 2
        ang = primitive_root_angles(n)
        lam1 = math.sqrt(n / 2)  # well-rounded λ_1 ~ sqrt(n/2)
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None:
                print(f" n={n} beta={beta}: no prize prime"); continue
            z = order_n_root(p, n)
            blog = math.log(p) / math.log(n)
            print(f"--- n={n} (D={D})  p={p} (2^{math.log2(p):.1f}, beta_eff={blog:.2f}); "
                  f"λ_1(wr)~{lam1:.2f}; sqrt(n)~{math.sqrt(n):.2f} ---")
            print(f"    {'r':>2} {'2r':>3} | {'T(distinct)':>11} {'mass':>8} {'|T_r|':>10} {'T*p/|Tr|':>9} | "
                  f"{'minHouse':>8} {'(2r)^φ':>11} {'minNorm':>11}")
            for r in range(2, 6):
                if math.comb(n + r - 1, r) > 1_500_000:  # multiset count cap
                    print(f"    {r:>2} {2*r:>3} |   (|multisets|~{math.comb(n+r-1,r):.2e} too large)")
                    continue
                st = sparse_defects(p, z, n, r, ang)
                Tr_size = math.comb(n + r - 1, r)  # # of x-side multisets (rough |T_r| upper)
                minN = math.exp(st['min_lognorm']) if not math.isnan(st['min_lognorm']) else float('nan')
                bound = (2 * r) ** D
                density = (st['T_distinct'] * p / Tr_size) if Tr_size else float('nan')
                print(f"    {r:>2} {2*r:>3} | {st['T_distinct']:>11} {st['mass']:>8} {Tr_size:>10} "
                      f"{density:>9.3f} | {st['min_house']:>8.2f} {bound:>11.2e} {minN:>11.1f}")
            print()
    print("KEY READINGS:")
    print(" - T(distinct) = # sparse-support ideal-SVP points (house<=2r AND signed-sum-of-<=2r-roots).")
    print(" - mass = exact E_r - E_r^(0) (the actual energy defect these contribute).")
    print(" - T*p/|T_r| ~ 1  => sparse defects obey the random 1/p density (no structured excess).")
    print(" - minHouse vs λ_1(wr)~√(n/2): is the SHORTEST sparse defect near the well-rounded minimum,")
    print("   or strictly longer (sparsity forces a longer shortest vector)?")
    print(" - minNorm vs (2r)^φ: where the norm-wall sits; minNorm >= p always (𝔭-membership).")


if __name__ == "__main__":
    main()
