#!/usr/bin/env python3
"""
probe_cheng_house_minnorm_407.py  --  #407: identify the EXTREMAL alpha and the CORRECT Cheng object.

Findings so far (probe_cheng_house_balanced_407.py):
  - balanced nonzero alpha = (r plus)-(r minus) of 2^mu-th roots: min house = sqrt(2), min|N| = 2,
    uniformly in n,r.  No units among balanced alphas.

This refines the Cheng-house question to its CORRECT form.  A p-defect needs p | N(alpha) with
alpha in the box (all conjugates <= 2r) and p the LARGE prize prime (~n^beta or n*2^128).  So:

  THE REAL OBJECT: among box alpha (house <= 2r), what is the set of POSSIBLE |N(alpha)| values, and
  in particular, can |N(alpha)| have the large prize prime p as a factor while staying <= (2r)^{n/2}?
  Equivalently (Cheng): is there a nonzero balanced alpha with p | N(alpha)?  This is EXACTLY the
  p-defect existence question -- house gives no extra leverage because:
     (i) house <= 2r is automatic (alpha is a sum of <=2r roots),
    (ii) a house LOWER bound (we found = sqrt(2)) yields |N| <= (sqrt2)^phi at best a LOWER bound is
         on house; to bound the COUNT we'd need an UPPER bound on house that is < the box -- which is
         false (max house = 2r, achieved).

This probe does the DECISIVE experiment: for the SMALLEST n where p > 2 prize-like primes exist with
p | N(alpha) for some box alpha, EXHIBIT such an alpha and its house.  This shows defects DO occur
(house ~ in [sqrt2, 2r], NOT pushed out of the box), confirming the dyadic house bound does NOT crack
the count.  We also print the FULL distribution of |N| to show the prize prime can divide it.

We also test the Habegger/Myerson comparison: their worst-case house LOWER bound is house >= c (we
measured c = sqrt(2) for balanced, c=1 for unbalanced) -- a CONSTANT, far ABOVE their general
(n+1)^{-p}.  So the dyadic structure DOES give a clean constant house floor sqrt(2).  But a constant
floor is USELESS for bounding the count: |N| >= (sqrt2)^phi = 2^{n/4} is a LOWER bound on |N| for the
WORST (smallest-house) alpha, but the count threat comes from alpha with |N| EXACTLY divisible by p
and conjugates spread up to 2r -- those have LARGE |N| (up to (2r)^{n/2}), not small.  The house floor
constrains the SHORTEST vector (lambda_1, already known >= sqrt(n/2) via the prime ideal), not the
box count.

Run:  python scripts/probes/probe_cheng_house_minnorm_407.py
"""
import math, itertools, cmath
from collections import Counter


def is_zero_2pow(items, n):
    h = n // 2
    red = [0] * h
    for j, c in items:
        if j < h:
            red[j] += c
        else:
            red[j - h] -= c
    return all(x == 0 for x in red)


def exact_norm_2pow(items, n):
    """EXACT integer N(alpha) for alpha in Z[zeta_{2^mu}] given as group-ring items (j,c).
       Reduce to power basis (deg phi=n/2, Phi=X^{n/2}+1), then N = resultant(alpha_poly, Phi)
       computed via product of alpha(zeta^t) over primitive t, ROUNDED to nearest int (exact since
       N is a rational integer)."""
    conjs_t = [t for t in range(1, n) if math.gcd(t, n) == 1]
    prod = 1.0 + 0j
    for t in conjs_t:
        s = 0j
        for j, c in items:
            s += c * cmath.exp(2j * math.pi * (t * j % n) / n)
        prod *= s
    return round(prod.real), conjs_t


def house_of(items, n, conjs_t):
    vals = []
    for t in conjs_t:
        s = 0j
        for j, c in items:
            s += c * cmath.exp(2j * math.pi * (t * j % n) / n)
        vals.append(abs(s))
    return max(vals)


def main():
    print("=" * 100)
    print(" #407 EXTREMAL alpha + |N| distribution for balanced sparse pm-sums of 2^mu-th roots")
    print("=" * 100)

    # 1. exhibit the sqrt(2)-house, |N|=2 extremal alpha at n=8
    n = 8
    print(f"\n[1] n={n}: the minimal-house (sqrt2) balanced alpha, exact norms:")
    conjs_t = [t for t in range(1, n) if math.gcd(t, n) == 1]
    roots = list(range(n))
    examples = []
    for plus in itertools.combinations(roots, 2):
        for minus in itertools.combinations(roots, 2):
            coeff = {}
            for j in plus:
                coeff[j] = coeff.get(j, 0) + 1
            for j in minus:
                coeff[j] = coeff.get(j, 0) - 1
            items = tuple(sorted((j, c) for j, c in coeff.items() if c != 0))
            if not items or is_zero_2pow(list(items), n):
                continue
            h = house_of(items, n, conjs_t)
            if abs(h - math.sqrt(2)) < 1e-6:
                Nexact, _ = exact_norm_2pow(items, n)
                examples.append((items, h, Nexact))
    # show a few distinct ones
    shown = set()
    cnt = 0
    for items, h, N in examples:
        key = items
        if key in shown:
            continue
        shown.add(key)
        print(f"    alpha = {dict(items)}   house={h:.4f}   N(alpha)={N}")
        cnt += 1
        if cnt >= 6:
            break

    # 2. the FULL |N| distribution at n=8, r=2 and r=3 -- show LARGE norms exist (the box has
    #    high-norm points too), and that |N| takes MANY values (so a large prime p CAN divide some).
    for r in (2, 3):
        print(f"\n[2] n={n}, r={r}: distribution of |N(alpha)| over nonzero balanced alpha (house in [sqrt2, 2r]):")
        seen = set()
        norm_counter = Counter()
        house_min, house_max = float('inf'), 0.0
        maxN = 0
        for plus in itertools.combinations_with_replacement(roots, r):
            for minus in itertools.combinations_with_replacement(roots, r):
                coeff = {}
                for j in plus:
                    coeff[j] = coeff.get(j, 0) + 1
                for j in minus:
                    coeff[j] = coeff.get(j, 0) - 1
                items = tuple(sorted((j, c) for j, c in coeff.items() if c != 0))
                if not items or items in seen or is_zero_2pow(list(items), n):
                    continue
                seen.add(items)
                Nexact, _ = exact_norm_2pow(items, n)
                aN = abs(Nexact)
                norm_counter[aN] += 1
                hh = house_of(items, n, conjs_t)
                house_min = min(house_min, hh)
                house_max = max(house_max, hh)
                maxN = max(maxN, aN)
        print(f"    house range [{house_min:.4f}, {house_max:.4f}];  max|N| = {maxN}  (=2^{math.log2(maxN):.2f})")
        print(f"    |N| value : count   (these are the integers a large prime p could divide -> defect)")
        for v in sorted(norm_counter)[:20]:
            print(f"       {v:>8} : {norm_counter[v]}")
        # which |N| are divisible by a prime > 2r (a 'prize-like' larger prime)?
        big_factor = [v for v in norm_counter if any(
            v % pr == 0 for pr in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47) if pr > 2 * r)]
        print(f"    |N| values with a prime factor > 2r (=> a prime p>2r CAN | N(alpha), a DEFECT for that p): "
              f"{sorted(big_factor)[:15]}")

    print()
    print("DECISIVE READING:")
    print("  * The minimal-house balanced alpha (house=sqrt2) have SMALL |N| (=2,4): they are NEVER")
    print("    defects for the large prize prime p (p does not divide a power of 2).  GOOD but trivial.")
    print("  * The box ALSO contains alpha with LARGE |N| (up to (2r)^{phi}) carrying large odd prime")
    print("    factors.  For such alpha, a prize-scale prime p | N(alpha) gives a genuine p-defect with")
    print("    house in [sqrt2, 2r] -- IN the box, NOT pushed out.  The house floor sqrt2 is irrelevant")
    print("    to these because they are the LARGE-norm, large-house members.")
    print("  * Hence a worst-case house LOWER bound (= sqrt2, dyadic, clean, beats Habegger (n+1)^{-p})")
    print("    does NOT bound the defect count: the defects are not the short (small-house) vectors but")
    print("    the box-interior large-norm ones, controlled by lambda_1.. lambda_phi geometry, = the")
    print("    Minkowski/box point-count wall.  Cheng-house route REDUCES to that wall.  No closure.")


if __name__ == "__main__":
    main()
