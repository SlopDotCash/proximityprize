#!/usr/bin/env python3
"""Order-64 (h=32) weight-{1,3} spectrum engine caveats beyond p = 65537.

Companion to Frontier/_G336Order64SpectrumEngineCaveat.lean (G336).

G333 closed off p = 65537 at this rung via g = 8224.  This probe records the
reusable collision engine

    2 * g^0 = g^a + g^b    (0 < a < b < h)

and four non-65537 instances where the same engine fires.  Injectivity contrast
at this rung remains the prize-scale Proth 21*2^128+1 (G333).

Findings at h = 32 (|D| = 39744):
  * p = 50177, g = 10433: NOT injective (25280 values).  Witness g^6 + g^8 = 2.
  * p = 51137, g = 6269:  NOT injective (26304 values).  Witness g^2 + g^14 = 2.
  * p = 78017, g = 27489: NOT injective (29632 values).  Witness g^2 + g^29 = 2.
  * p = 97729, g = 11143: NOT injective (30720 values).  Witness g^8 + g^9 = 2.

What this does NOT do: no field-uniform theorem, no production claim, no delta*
movement.  Does not restate the G333 65537 instance.

Stdlib only, exact integer arithmetic, no floats.

Usage:  python3 probe_order64_engine_caveats.py
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
    # m = 64 = 2^6; proper 2-power divisors
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
    h = 32
    law = 2 * h + 8 * (h * (h - 1) * (h - 2) // 6)  # 39744
    assert law == 39744

    # (p, g, a, b, expected_distinct)
    deficient = [
        (50177, 10433, 6, 8, 25280),
        (51137, 6269, 2, 14, 26304),
        (78017, 27489, 2, 29, 29632),
        (97729, 11143, 8, 9, 30720),
    ]

    print("# G336 probe: h=32 (|D|=%d) engine caveats" % law)
    print("# p        g        ord64 distinct  def   witness")
    for p, g, a, b, expect in deficient:
        assert is_prime(p) and (p - 1) % 64 == 0
        assert has_order(g, p, 64), (p, g)
        assert (pow(g, a, p) + pow(g, b, p)) % p == 2
        assert pow(g, 32, p) == p - 1
        dist = spectrum_card(p, g, h)
        print(
            "  %-8d %-8d yes  %-9d %-5d g^%d + g^%d = 2"
            % (p, g, dist, law - dist, a, b)
        )
        assert dist == expect, (p, dist, expect)
        assert dist < law and p > law

    print(
        "# PASS: deficient {50177:25280, 51137:26304, 78017:29632, 97729:30720}; "
        "G333 Proth control remains the injective contrast"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
