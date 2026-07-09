#!/usr/bin/env python3
"""
probe_cheng_house_dyadic_407.py  --  #407 CHENG-HOUSE ROUTE.

Cheng et al. (J.Number Theory 2022, "Solution counts and sums of roots of unity") equate the
p-defect count to LOWER bounds on the HOUSE of sparse sums of n-th roots of unity. A p-defect is a
nonzero
        alpha = (sum of <=r of the n-th roots) - (sum of <=r of the n-th roots)  in Z[zeta_n]
with p | N(alpha). For alpha to be COUNTED in the prize box B_r it must have ALL conjugates
|sigma(alpha)| <= 2r (it is a balanced sum of <=2r roots of unity, so its house is automatically
<=2r -- that is NOT the constraint). The constraint that controls the COUNT is the LOWER side:

    HOW SMALL can house(alpha) = max_sigma |sigma(alpha)| be for a NONZERO such alpha?

The norm route says |N(alpha)| <= house(alpha)^{phi(n)}; if we had a worst-case house LOWER bound
    house(alpha) >= c > 1  (uniform, for every nonzero sparse pm-sum)
then |N(alpha)| >= c^{phi(n)} = c^{n/2}, which EXCEEDS the prize p = n^beta once n/2 * log c > beta log n,
i.e. n >> beta log n / log c -- i.e. for ALL large n. Then p | N(alpha) with |N(alpha)|>=p would
NOT by itself forbid the defect; the relevant thing is the COUNT of alpha in the box, controlled by
how the houses distribute.

THE KEY DICHOTOMY this probe resolves:
  (a) If min house over nonzero sparse pm-sums is BOUNDED BELOW by c>1 uniformly in n  ==>  the
      Cheng route gives |N(alpha)|>=c^{n/2}, the lattice is "fat", FEW points in any box, GOOD.
  (b) If min house -> 1 (or worse, can be made <1) as n grows  ==>  there exist nonzero alpha with
      ALL conjugates near/below 1, |N(alpha)| can be ~1 (a unit-like element) or grow only slowly,
      the lattice has SHORT vectors, MANY defects possible, the route STALLS (Minkowski wall).

Habegger/Myerson worst-case house LOWER bound is only EXPONENTIALLY SMALL: house >= (n+1)^{-...}.
This probe asks: does the DYADIC n=2^mu structure (antipodal: zeta^{n/2} = -1; Lam-Leung tower)
give a BETTER (bounded-below) worst-case house, enough to make |N(alpha)| outgrow the box count?

We brute-force, for n=2^mu (mu small), over ALL nonzero alpha = signed sums of <=2r of the n-th
roots of unity (r small), the MINIMAL house and minimal |N(alpha)|, and report:
  - min_house(n,r): the worst-case (smallest) house of a nonzero such alpha;
  - min_absnorm(n,r): the smallest |N(alpha)| over nonzero such alpha;
  - whether any alpha is a UNIT (|N|=1) or near-unit (house<=1).

If min_house stays >= c>1, the dyadic structure CRACKS the worst-case house bound (closure shot).
If min_house -> 1, the route is walled (the expected outcome; we want to PIN it precisely).

Run:  python scripts/probes/probe_cheng_house_dyadic_407.py
"""
import math, itertools, cmath
from collections import defaultdict


def primitive_conjugates(n):
    """The phi(n) primitive n-th roots of unity (Galois conjugates of zeta_n)."""
    return [cmath.exp(2j * math.pi * t / n) for t in range(1, n) if math.gcd(t, n) == 1]


def all_roots(n):
    """All n-th roots of unity zeta^j, j=0..n-1, as their EXPONENTS (we work symbolically: alpha is
       a multiset of signed exponents; conjugation sends zeta -> zeta^t for t coprime to n)."""
    return list(range(n))


def house_and_norm(coeff, n, conjs_t):
    """coeff: dict j -> integer coeff of zeta^j (group-ring, length n).  Returns (house, |N|) where
       conjugation sigma_t sends zeta^j -> zeta^{tj mod n}.  house = max_t |sigma_t(alpha)|,
       |N| = prod_t |sigma_t(alpha)| over t coprime to n (phi(n) embeddings, but each primitive root
       gives a distinct embedding; we use the phi(n) primitive-root exponents)."""
    vals = []
    for t in conjs_t:
        s = 0j
        for j, c in coeff.items():
            if c:
                s += c * cmath.exp(2j * math.pi * (t * j % n) / n)
        vals.append(abs(s))
    house = max(vals)
    # |N(alpha)| = product over the phi(n) embeddings.  But sigma_t for t coprime to n gives exactly
    # the phi(n) conjugates of the ALGEBRAIC NUMBER alpha (after reduction mod Phi_n the group-ring
    # element alpha maps to an element of Q(zeta_n); its conjugates are sigma_t(alpha), t in (Z/n)^*).
    absN = 1.0
    for v in vals:
        absN *= v
    return house, absN, vals


def gen_signed_sparse(n, total):
    """Generate all alpha = signed sums of EXACTLY `total` of the n-th roots (with signs +/-1),
       as group-ring coeff dicts.  We deduplicate by the resulting coefficient vector.
       To keep it finite & meaningful for HOUSE-MINIMIZATION we restrict to {-1,0,1} coeffs of
       Hamming weight <= total (these are EXACTLY the sparse pm-sums of <=total roots; this is the
       Cheng object -- balanced or not).  We also enforce alpha != 0 in Z[zeta_n]."""
    roots = all_roots(n)
    seen = set()
    for w in range(1, total + 1):
        for support in itertools.combinations(roots, w):
            for signs in itertools.product((-1, 1), repeat=w):
                coeff = {j: 0 for j in range(n)}
                for j, sg in zip(support, signs):
                    coeff[j] = sg
                key = tuple(coeff[j] for j in range(n))
                if key in seen:
                    continue
                seen.add(key)
                yield coeff


def is_zero_in_cyclotomic(coeff, n):
    """alpha = sum coeff[j] zeta^j == 0 in Z[zeta_n] iff its reduction mod Phi_n is 0 iff
       Phi_n | (sum coeff[j] X^j).  For n=2^mu, Phi_n = X^{n/2}+1, so reduce: coeff[j] for j>=n/2
       subtract into coeff[j-n/2].  alpha==0 iff all reduced coeffs ==0."""
    h = n // 2
    red = [0] * h
    for j in range(n):
        c = coeff[j]
        if c == 0:
            continue
        if j < h:
            red[j] += c
        else:
            red[j - h] -= c   # zeta^{j} = -zeta^{j-h} since zeta^h = -1
    return all(x == 0 for x in red)


def main():
    print("=" * 100)
    print(" #407 CHENG-HOUSE (dyadic):  worst-case (MINIMAL) house & |N| of nonzero sparse pm-sums of")
    print(" the n-th roots of unity, n=2^mu.  Does the antipodal/tower structure force house bounded")
    print(" below by c>1 (=> |N|>=c^{n/2} >> box, route CRACKS) or -> 1 (=> short vectors, WALL)?")
    print("=" * 100)
    print(f"  {'mu':>3} {'n':>5} {'phi':>4} {'2r':>3} {'#alpha':>9} {'minHouse':>9} {'minHouse@nonzero':>16}"
          f" {'min|N|':>9} {'#units(|N|=1)':>13} {'#house<=1':>10}")
    for mu in range(2, 7):
        n = 1 << mu
        phi = n // 2
        conjs_t = [t for t in range(1, n) if math.gcd(t, n) == 1]
        for two_r in (2, 3, 4):
            if two_r > n:
                continue
            count = 0
            min_house = float('inf')
            min_house_nonzero = float('inf')
            min_absN = float('inf')
            n_units = 0
            n_house_le1 = 0
            # cap the work for big n
            if n >= 32 and two_r >= 4:
                continue
            for coeff in gen_signed_sparse(n, two_r):
                if is_zero_in_cyclotomic(coeff, n):
                    continue
                count += 1
                house, absN, vals = house_and_norm(coeff, n, conjs_t)
                min_house = min(min_house, house)
                if house > 1e-9:
                    min_house_nonzero = min(min_house_nonzero, house)
                min_absN = min(min_absN, absN)
                if abs(absN - 1.0) < 1e-6:
                    n_units += 1
                if house <= 1.0 + 1e-9:
                    n_house_le1 += 1
            print(f"  {mu:>3} {n:>5} {phi:>4} {two_r:>3} {count:>9} {min_house:>9.4f} "
                  f"{min_house_nonzero:>16.4f} {min_absN:>9.4f} {n_units:>13} {n_house_le1:>10}")
    print()
    print("INTERPRETATION:")
    print("  * min|N| is the smallest |norm| of a nonzero sparse pm-sum: this is the per-alpha")
    print("    threshold p must beat for the NORM bound to kill that alpha as a defect (need p>min|N|).")
    print("  * If min|N| stays SMALL (e.g. ~1, units) while n grows  ==>  there exist alpha with tiny")
    print("    norm whose conjugates are ALL small (in the box) -- the WALL: a single short vector p|N")
    print("    survives for infinitely many p, the count is not killed by norm.")
    print("  * If minHouse stays >= c>1  ==>  no near-unit, |N|>=c^{n/2}, route cracks.")
    print("  KEY: a UNIT sparse pm-sum (|N|=1, all conjugates ~1) is the EXTREMAL defect-enabler.")


if __name__ == "__main__":
    main()
