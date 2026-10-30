#!/usr/bin/env python3
"""Order-32 (h=16) weight-{1,3} spectrum engine caveats beyond p = 65537.

Companion to Frontier/_G334Order32SpectrumEngineCaveat.lean (G334).

G331 / PR #292 closed off p = 65537 at this rung via g = -8.  This probe records
the reusable collision engine

    2 * g^0 = g^a + g^b    (0 < a < b < h)

and four non-Fermat instances where the same engine fires, plus three injective
controls for contrast.

Findings at h = 16 (|D| = 4512):
  * p = 194977, g = 180906: NOT injective (3616 values).  Witness g^8 + g^13 = 2.
  * p = 156353, g = 9347:   NOT injective (3584 values).  Witness g^1 + g^14 = 2.
  * p = 50177,  g = 7713:   NOT injective (3584 values).  Witness g^1 + g^12 = 2.
  * p = 37217,  g = 32508:  NOT injective (3584 values).  Witness g^4 + g^15 = 2.
  * Controls: p = 16033, 786433, 6700417 are injective (4512 values).

What this does NOT do: no field-uniform theorem, no production claim, no delta*
movement.  Does not restate the G331 65537 instance.

Stdlib only, exact integer arithmetic, no floats.

Usage:  python3 probe_order32_engine_caveats.py
"""
from itertools import combinations


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def has_order(g, p, m):
    """True iff g has exact order m in F_p (assumes m | p-1)."""
    if pow(g, m, p) != 1:
        return False
    # m = 32 = 2^5; proper divisors are 1,2,4,8,16
    d = m
    while d > 1:
        d //= 2
        if pow(g, d, p) == 1:
            return False
    return True


def spectrum_card(p, g, h, weights=(1, 3)):
    """Exact cardinality of signed sums for weight set A over half-window."""
    pows = [pow(g, i, p) for i in range(h)]
    vals = set()
    for a in weights:
        for U in combinations(range(h), a):
            for k in range(a + 1):
                for T in combinations(U, k):
                    Tset = set(T)
                    s = 0
                    for i in U:
                        if i in Tset:
                            s = (s + pows[i]) % p
                        else:
                            s = (s - pows[i]) % p
                    vals.add(s)
    return len(vals)


def main():
    h = 16
    law = 2 * h + 8 * (h * (h - 1) * (h - 2) // 6)  # 4512
    assert law == 4512

    # (p, g, a, b, expected_distinct)
    deficient = [
        (194977, 180906, 8, 13, 3616),
        (156353, 9347, 1, 14, 3584),
        (50177, 7713, 1, 12, 3584),
        (37217, 32508, 4, 15, 3584),
    ]
    # (p, g) injective controls; generators precomputed
    injective = [
        (16033, 262),
        (786433, 5),
        (6700417, 5),
    ]

    print("# G334 probe: h=16 (|D|=%d) engine caveats" % law)
    print("# p        g        ord32 distinct  def   witness")
    for p, g, a, b, expect in deficient:
        assert is_prime(p) and (p - 1) % 32 == 0
        assert has_order(g, p, 32), (p, g)
        assert (pow(g, a, p) + pow(g, b, p)) % p == 2
        dist = spectrum_card(p, g, h)
        print("  %-8d %-8d yes  %-9d %-5d g^%d + g^%d = 2" %
              (p, g, dist, law - dist, a, b))
        assert dist == expect, (p, dist, expect)
        assert dist < law and p > law

    print("# controls (expect injective = %d)" % law)
    for p, g in injective:
        assert is_prime(p) and (p - 1) % 32 == 0
        # If precomputed g fails order, search quickly via (p-1)/32 factor
        if not has_order(g, p, 32):
            g = None
            fac = (p - 1) // 32
            for base in range(2, 200):
                cand = pow(base, fac, p)
                if has_order(cand, p, 32):
                    g = cand
                    break
            assert g is not None, "no order-32 root at %d" % p
        dist = spectrum_card(p, g, h)
        print("  %-8d %-8d yes  %-9d %-5d (injective)" %
              (p, g, dist, law - dist))
        assert dist == law, (p, dist)

    print("# PASS: deficient {194977:3616, 156353:3584, 50177:3584, 37217:3584}; "
          "injective controls {16033,786433,6700417}")


if __name__ == "__main__":
    main()
