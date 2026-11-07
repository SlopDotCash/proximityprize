#!/usr/bin/env python3
"""n=64 t=4 below-ceiling census at two further prize-scale Proth primes.

Object.  Same finite-field event as ``probe_n64_below_ceiling_max.py``: for a
prime ``p = 1 (mod 64)``, a generator ``g`` of order ``n = 64``, the smooth
domain ``x_i = g^i`` and the dimension-two code of affine words ``c0 + c1*x``,
a scalar ``gamma`` is *below-ceiling bad* for the monomial pencil
``(u0,u1) = (x^a, x^b)`` when ``u0 + gamma*u1`` agrees with an affine word on
some 4-subset ``S`` while ``(u0,u1)`` is not jointly affine on ``S``.

New parameter points (the claim of this probe).  Full census over all 4096
ordered monomial pencils at the two further prize-scale Proth primes

    p = 111*2^128 + 1   (Proth witness 5),
    p = 123*2^128 + 1   (Proth witness 7),

in addition to ``p = 21*2^128 + 1`` from the base probe.  At each new prime the
probe reports the t=4 below-ceiling maximum, its maximizer set, the (3,2) t=3
ceiling count, the t=3 maximum, and the full-census checksums.  It also
asserts that the entire 4096-entry t=4 count vector is *identical* at the three
prize-scale primes (not only the maximum), so the prize-scale census is
field-independent on the tested set; the small primes 12289 and 65537 have
different vectors and smaller maxima.

Independent cross-checks (all three must agree on the same integers):

  1. ``probe_n64_below_ceiling_max.census``: direct collinearity-determinant
     census over 4-subsets, one gamma per subset;
  2. ``probe_n64_below_ceiling_max_crosscheck.coset_counts``: shape/orbit
     census through the complete-homogeneous closed form and translation
     cosets of ``mu_64``; it never enumerates 4-subsets, and the two
     checksums pin agreement on every one of the 4096 pencils;
  3. ``literal_count`` below: a third, inline derivation that walks every
     4-subset, solves the two collinearity conditions for ``gamma`` directly,
     and checks the ``pairJointAgreesOn`` exclusion on the subset.  It is run
     on every maximizer pencil at each prime and on all 64 pencils at n=8,
     where the published G310/G328 below-ceiling maximum 9 applies.

Scope.  Finite fields only; fixed rung ``n = 64``; monomial pencils only --
not a maximum over arbitrary word pairs.  Nothing here is a production
statement (``n = 2^30/2^32``), a ``delta*`` claim, or a step toward the prize.
Stdlib only, integer arithmetic only, deterministic.
"""

import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_n64_below_ceiling_max as base  # noqa: E402
import probe_n64_below_ceiling_max_crosscheck as cc  # noqa: E402

N = 64
PRIZE_EXP = 128
CASES = ((111, 5), (123, 7))
G328_BELOW_MAX = 9


def literal_count(xs, a, b, p):
    """Literal t=4 bad-scalar count of one pencil by 4-subset enumeration.

    For a 4-subset with anchored triples T0 = (i,j,k) and T1 = (i,j,l) the
    collinearity conditions D_a(T) + gamma*D_b(T) = 0 on both triples are
    solved for gamma directly.  A subset is excluded when both words are
    affine on it (the pairJointAgreesOn exclusion).
    """
    n = len(xs)
    ua = [pow(x, a, p) for x in xs]
    ub = [pow(x, b, p) for x in xs]
    bad = set()
    for i, j, k, l in combinations(range(n), 4):
        xi = xs[i]
        dxj = (xs[j] - xi) % p
        dxk = (xs[k] - xi) % p
        dxl = (xs[l] - xi) % p
        da0 = (dxj * (ua[k] - ua[i]) - dxk * (ua[j] - ua[i])) % p
        db0 = (dxj * (ub[k] - ub[i]) - dxk * (ub[j] - ub[i])) % p
        da1 = (dxj * (ua[l] - ua[i]) - dxl * (ua[j] - ua[i])) % p
        db1 = (dxj * (ub[l] - ub[i]) - dxl * (ub[j] - ub[i])) % p
        if da0 == 0 and da1 == 0 and db0 == 0 and db1 == 0:
            continue  # jointly affine on the 4-subset: excluded
        if db0:
            gamma = (-da0) * pow(db0, -1, p) % p
            if (da1 + gamma * db1) % p:
                continue
        elif da0:
            continue
        elif db1:
            gamma = (-da1) * pow(db1, -1, p) % p
        elif da1:
            continue
        else:
            raise AssertionError(
                f"all gammas bad on one 4-subset of ({a},{b}) mod {p}")
        bad.add(gamma)
    return len(bad)


def proth_prime(k, witness):
    p = k * (2 ** PRIZE_EXP) + 1
    assert k % 2 == 1 and k < 2 ** PRIZE_EXP
    assert pow(witness, (p - 1) // 2, p) == p - 1, (k, witness)
    return p


def main():
    print("n=64 t=4 below-ceiling census at further prize-scale Proth primes")
    print("implementations: direct determinants, shape/orbit cosets, "
          "literal 4-subset solve")

    # Anchor: the literal 4-subset solve on every n=8 pencil at p=41 must give
    # the published G310/G328 maximum 9 at the four published pencils.
    _, counts_ceiling, counts_below = base.census(8, 41)
    literal_below = {(a, b): literal_count(base.census(8, 41)[0], a, b, 41)
                     for a in range(8) for b in range(8)}
    assert literal_below == dict(counts_below), "literal n=8 != direct census"
    maximum, winners = base.summarize(literal_below)
    assert maximum == G328_BELOW_MAX and winners == base.G328_WINNERS, (
        maximum, winners)
    print(f"n=8 p=41 anchor: literal 4-subset solve reproduces max "
          f"{maximum} at {winners} on all 64 pencils")

    vectors = {}
    for k, witness in CASES:
        p = proth_prime(k, witness)
        xs, counts_ceiling, counts_below = base.census(N, p)
        vectors[k] = counts_below
        maximum, winners = base.summarize(counts_below)
        t3_top, t3_winners = base.summarize(counts_ceiling)
        stack = counts_ceiling[(3, 2)]
        sums = base.checksum(counts_below, N)
        assert 2 * maximum <= N * (N - 1) * (N - 2) // 6, (k, maximum)
        print(f"k={k} p={p}: (3,2) t=3 {stack}; t=3 max {t3_top} "
              f"({len(t3_winners)} pencils)")
        print(f"  t=4 below max {maximum} at {winners}")
        print(f"  t=4 census checksum: sum {sums[0]}, weighted {sums[1]}")

        cc_ceiling, cc_below = cc.coset_counts(N, p)
        cc_sums = cc.checksum(cc_below, N)
        assert cc_sums == sums, (k, cc_sums, sums)
        assert cc.summarize(cc_below) == (maximum, winners), (
            k, cc.summarize(cc_below), (maximum, winners))
        assert cc.summarize(cc_ceiling)[0] == t3_top, (k,)
        print(f"  shape/orbit census: same max, winners and both checksums")

        for a, b in winners:
            literal = literal_count(xs, a, b, p)
            assert literal == maximum, (k, a, b, literal, maximum)
        print(f"  literal 4-subset audit agrees on all {len(winners)} maximizers")

    p21 = base.prize_prime()
    vectors[21] = base.census(N, p21)[2]
    reference = vectors[CASES[0][0]]
    for k in vectors:
        assert vectors[k] == reference, (k, "t=4 count vector differs")
    print(f"t=4 count vector identical at k=21, {CASES[0][0]}, {CASES[1][0]}: "
          f"all {len(reference)} entries, max {max(reference.values())}")

    print("PASS: n=64 t=4 below-ceiling census on all 4096 monomial pencils "
          "at p = 111*2^128+1 and 123*2^128+1; three implementations agree and "
          "the count vector matches p = 21*2^128+1")


if __name__ == "__main__":
    main()
