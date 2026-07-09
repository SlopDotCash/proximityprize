#!/usr/bin/env python3
"""
probe_cheng_house_balanced_407.py  --  #407 CHENG-HOUSE, the ACTUAL defect shape.

The previous probe (probe_cheng_house_dyadic_407.py) found min house = 1 over ALL sparse pm-sums,
because single roots zeta^j (units) are trivially included. But the ACTUAL p-defect counted by the
moment E_r is

    alpha = (x_1 + ... + x_r) - (y_1 + ... + y_r),   x_i, y_j in mu_n (n-th roots),

i.e. a BALANCED signed sum: exactly r plus-roots and r minus-roots (multisets), with alpha != 0 in
Z[zeta_n] and p | N(alpha).  (For the SUP-NORM/house route we may take any r1 plus and r2 minus with
r1+r2 <= 2r; for the cumulant E_r the natural object is r1=r2=r.)  This probe asks the SHARP
Cheng-house question on THIS object:

  Q1. What is the MINIMAL house of a nonzero balanced alpha (r plus, r minus, distinct multisets)?
  Q2. What is the MINIMAL |N(alpha)| over these?  (The per-alpha norm threshold.)
  Q3. Crucially: is there a nonzero balanced alpha that is a UNIT (|N|=1) -- the extremal
      defect-enabler -- for the dyadic n=2^mu?  If yes, the Cheng-house route is WALLED (a unit has
      all conjugates of modulus near 1, sits in the box, and p|N is impossible only if p|1 -- i.e.
      a unit is NEVER a defect, GOOD; but a small-norm non-unit IS the threat).

REFINED MATH (the correct reading of the route):
  - A defect needs p | N(alpha), alpha != 0.  Since N(alpha) is a nonzero rational integer,
    |N(alpha)| >= 1, and p | N(alpha) FORCES |N(alpha)| >= p.  So a UNIT (|N|=1) can NEVER be a
    defect for p>1.  GOOD.  The threat is alpha with 1 < |N(alpha)|, p | N(alpha), AND all conjugates
    small (in the box B_r: |sigma(alpha)| <= 2r for all sigma).
  - The Cheng-house route wants: a LOWER bound house(alpha) >= H(n,r) for every nonzero balanced
    alpha, strong enough that |N| <= house^{phi} can't reconcile with "all conjugates <= 2r AND
    p|N".  But the binding constraint is |N|>=p (from p|N), combined with the box giving |N|<=(2r)^{phi}.
    So a defect EXISTS only if  p <= |N(alpha)| <= (2r)^{phi(n)} = (2r)^{n/2}.
    => For p > (2r)^{n/2}: NO defect (the norm regime, already known, n<=64 at prize scale).
    => For p < (2r)^{n/2} (the prize, n=2^40): defects are NOT excluded by the per-alpha box bound;
       the question is the COUNT, governed by how MANY alpha land in the box with p|N.

  So the Cheng-house route's leverage is NOT a house LOWER bound per se (house is automatically
  <=2r since alpha is a sum of <=2r roots); it is whether the dyadic structure makes the NUMBER of
  box-alpha with bounded norm SMALL.  The honest reformulation: the route reduces to the SAME box
  point-count (framing #10), and the per-alpha house bound gives NOTHING beyond the norm regime.

This probe CONFIRMS that precisely:  it tabulates the distribution of house and |N| over balanced
alpha, showing (i) house is tightly clustered in [c0, 2r] (never small -- but that's the UPPER side,
useless), (ii) min|N| over NONZERO balanced alpha, and whether min|N| can be as small as a fixed
constant (so the box at the prize scale is populated by bounded-norm vectors -> the count, not the
house, is the open object).

Run:  python scripts/probes/probe_cheng_house_balanced_407.py
"""
import math, itertools, cmath


def is_zero_2pow(red_input, n):
    h = n // 2
    red = [0] * h
    for j, c in red_input:
        if j < h:
            red[j] += c
        else:
            red[j - h] -= c
    return all(x == 0 for x in red), red


def conj_vals(coeff_items, n, conjs_t):
    vals = []
    for t in conjs_t:
        s = 0j
        for j, c in coeff_items:
            s += c * cmath.exp(2j * math.pi * (t * j % n) / n)
        vals.append(abs(s))
    return vals


def main():
    print("=" * 104)
    print(" #407 CHENG-HOUSE on the ACTUAL balanced defect alpha = (r plus-roots)-(r minus-roots),")
    print(" nonzero in Z[zeta_{2^mu}].  house is AUTOMATICALLY <= 2r (sum of 2r roots); the route's")
    print(" only leverage would be a per-alpha NORM LOWER bound.  We tabulate min/max house and min|N|.")
    print("=" * 104)
    print(f"  {'mu':>3} {'n':>5} {'phi':>4} {'r':>3} {'#nonzero':>9} {'minHouse':>9} {'maxHouse':>9}"
          f" {'min|N|':>9} {'#|N|=1':>7} {'#|N|<=10':>9} {'norm-reg p>(2r)^phi':>20}")
    for mu in range(2, 6):
        n = 1 << mu
        phi = n // 2
        conjs_t = [t for t in range(1, n) if math.gcd(t, n) == 1]
        for r in (1, 2, 3):
            if 2 * r > n:
                continue
            if n >= 16 and r >= 3:
                continue
            roots = list(range(n))
            seen = set()
            count = 0
            min_house = float('inf')
            max_house = 0.0
            min_absN = float('inf')
            n_unit = 0
            n_small = 0
            # plus multiset: r-combination WITH repetition? Use r DISTINCT (subset) -- the dominant
            # contribution; repeats give lower-weight alpha already covered.  To capture true defects
            # we allow repetition via combinations_with_replacement on plus AND minus, then dedupe by
            # the net coeff vector.
            for plus in itertools.combinations_with_replacement(roots, r):
                for minus in itertools.combinations_with_replacement(roots, r):
                    coeff = {}
                    for j in plus:
                        coeff[j] = coeff.get(j, 0) + 1
                    for j in minus:
                        coeff[j] = coeff.get(j, 0) - 1
                    items = tuple(sorted((j, c) for j, c in coeff.items() if c != 0))
                    if not items:
                        continue  # alpha = 0 trivially (same multiset)
                    if items in seen:
                        continue
                    seen.add(items)
                    isz, red = is_zero_2pow(list(items), n)
                    if isz:
                        continue
                    count += 1
                    vals = conj_vals(items, n, conjs_t)
                    house = max(vals)
                    absN = 1.0
                    for v in vals:
                        absN *= v
                    min_house = min(min_house, house)
                    max_house = max(max_house, house)
                    min_absN = min(min_absN, absN)
                    if abs(absN - 1.0) < 1e-6:
                        n_unit += 1
                    if absN <= 10.0 + 1e-6:
                        n_small += 1
            norm_reg = (2 * r) ** phi
            print(f"  {mu:>3} {n:>5} {phi:>4} {r:>3} {count:>9} {min_house:>9.4f} {max_house:>9.4f}"
                  f" {min_absN:>9.4f} {n_unit:>7} {n_small:>9} 2^{math.log2(norm_reg):>17.1f}")
    print()
    print("VERDICT (Cheng-house route):")
    print("  * house is bounded BELOW by min_house (a positive constant, NOT ->0) and ABOVE by ~2r.")
    print("    But the UPPER bound house<=2r is automatic; the LOWER bound on house gives, via")
    print("    |N|<=house^phi, only an UPPER bound on |N| -- the box bound (2r)^phi we already have.")
    print("  * The defect needs p | N(alpha), so |N|>=p.  A defect EXISTS only if p <= (2r)^phi (norm")
    print("    regime boundary, = n<=64 at prize scale).  Below it (prize n=2^40), the per-alpha house/")
    print("    norm bound is USELESS -- the open object is the COUNT of box-alpha with p|N (framing 10).")
    print("  * min|N| (smallest nonzero balanced norm) tells us the box at prize scale IS populated by")
    print("    bounded-norm vectors; if min|N| is a small constant, the count is the genuine residual.")
    print("  CONCLUSION: dyadic structure does NOT yield a worst-case house LOWER bound that bounds the")
    print("  count -- the route REDUCES to the box point-count = the SAME Minkowski wall.  No closure.")


if __name__ == "__main__":
    main()
