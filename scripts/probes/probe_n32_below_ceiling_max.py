#!/usr/bin/env python3
"""Exact n=32 dimension-two below-ceiling monomial-pencil census (next rung).

The n=8 rung is G310/G328 (below-ceiling maximum 9 at ``(x^4,x^3)``); the n=16
rung is ``probe_n16_below_ceiling_max.py`` (maximum 97 at
``(8,7),(8,15),(9,2),(9,10)``).  This probe climbs to ``n = 32`` on ``mu_32``
for a fixed list of primes, at the below-ceiling agreement threshold ``t = 4``
of the KKH26 dimension-two slice, and also records the ``t = 3`` ceiling census.

Object.  Fix a prime ``p = 1 (mod n)``, a generator ``g`` of order ``n`` in
``F_p``, the smooth domain ``x_i = g^i``, and the dimension-two code of affine
words ``c0 + c1*x``.  For a monomial pencil ``(u0,u1) = (x^a, x^b)`` the bad
scalars are the ``gamma`` for which ``u0 + gamma*u1`` agrees with an affine
word on some set ``S`` with ``|S| >= t`` while ``(u0,u1)`` is not jointly affine
on ``S`` (the ``pairJointAgreesOn`` exclusion of the repository MCA event).

Exact characterisation used here (this is the whole algorithm):

  For ``t = 3``:  gamma is bad iff some triple T has ``D_b(T) != 0`` and
  ``D_a(T) + gamma*D_b(T) = 0``, where ``D_e(T)`` is the 2x2 collinearity
  determinant of ``(x_i, x_i^e)`` on T.  ``D_b(T) != 0`` says ``u1`` is not
  affine on T, so the witness is not jointly affine.

  For ``t = 4``:  gamma is bad iff some 4-subset S is collinear for gamma and
  some triple of S has ``D_b != 0``.  Checking the base triple ``(s0,s1,s2)``
  and the triple ``(s0,s1,s3)`` that contains the fourth point decides this.

Both are exact iff-characterisations: a bad gamma has a witness set on which
``u1`` is non-affine (if ``u1`` were affine there, then ``u0 = (u0+gamma*u1) -
gamma*u1`` would be affine too, contradicting the exclusion), hence a witness
triple with ``D_b != 0``; conversely the produced triples are valid witnesses.
No floating point is used anywhere.

Scope (read before citing): finite fields only; fixed rungs n = 8, 16 and the
new rung n = 32; monomial pencils only (NOT a maximum over all stacks).  The
n = 32 census runs over every prime p = 1 (mod 32) in [97, 20000], plus the
Fermat prime 65537 and the prize-scale Proth prime 21*2^128+1.  This is not a
field-uniform theorem, not a production n = 2^30/2^32 statement, and says
nothing about delta* or the prize.  The n = 32 numbers are new finite data; the
n = 8 and n = 16 integers are reproductions through a different algorithm.
"""

from itertools import combinations
from math import isqrt

T_CEIL = 3
T_BELOW = 4
LIMIT = 20_000

# Below-ceiling good-side bound proved in KKH26DimTwoPin.lean:
# #bad * 12 <= n(n-1)(n-2).
GOOD_BOUND = {8: 28, 16: 280, 32: 2480}

G328_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))
FOUR = ((8, 7), (8, 15), (9, 2), (9, 10))

# Published n=16 spot values from probe_n16_below_ceiling_max.py:
# p -> (t=3 ceiling count, t=4 below-ceiling max, maximizers or None).
N16_SPOT = {
    17: (17, 17, None),
    97: (96, 97, ((8, 15), (9, 2))),
    113: (112, 97, ((8, 7), (9, 10))),
    193: (192, 97, FOUR),
    241: (240, 97, ((8, 15), (9, 2))),
    257: (224, 97, ((8, 15), (9, 2))),
    337: (272, 97, FOUR),
    353: (272, 81, FOUR),
    449: (336, 97, ((8, 15), (9, 2))),
    1201: (464, 97, FOUR),
    1217: (448, 97, ((8, 15), (9, 2))),
    12289: (464, 97, FOUR),
    19489: (464, 97, FOUR),
    65537: (464, 97, FOUR),
}

# Fixed n=32 profile: t=4 below-ceiling maximum over all 1024 monomial pencils at
# every prime p = 1 (mod 32) in [97, LIMIT].
N32_T4 = {
    97: 97, 193: 193, 257: 257, 353: 353, 449: 449, 577: 385, 641: 481, 673: 577, 769: 641,
    929: 609, 1153: 673, 1217: 577, 1249: 769, 1409: 769, 1601: 801, 1697: 769, 1889: 801,
    2017: 737, 2081: 801, 2113: 609, 2273: 801, 2593: 865, 2657: 801, 2689: 865, 2753: 865,
    3041: 897, 3137: 769, 3169: 865, 3329: 865, 3361: 865, 3457: 801, 3617: 833, 4001: 865,
    4129: 865, 4289: 865, 4481: 865, 4513: 897, 4673: 833, 4801: 897, 4993: 865, 5153: 897,
    5281: 897, 5441: 833, 5569: 833, 5857: 865, 5953: 897, 6113: 897, 6337: 833, 6529: 897,
    6689: 865, 6977: 897, 7297: 897, 7393: 865, 7457: 865, 7489: 865, 7649: 897, 7681: 833,
    7841: 865, 7873: 897, 7937: 897, 8161: 897, 8353: 865, 8513: 897, 8609: 865, 8641: 865,
    8737: 897, 8929: 897, 9281: 865, 9377: 897, 9473: 897, 9601: 897, 9697: 897, 9857: 865,
    10177: 865, 10273: 865, 10337: 897, 10369: 865, 10433: 897, 10529: 865, 10657: 833,
    10753: 897, 11329: 865, 11393: 897, 11489: 897, 11617: 897, 11681: 865, 11777: 897,
    11969: 865, 12097: 865, 12161: 865, 12289: 865, 12577: 865, 12641: 897, 13121: 865,
    13217: 897, 13249: 897, 13313: 865, 13441: 897, 13537: 897, 13633: 865, 13697: 897,
    13729: 897, 13921: 897, 14081: 897, 14177: 897, 14369: 833, 14401: 897, 14561: 865,
    14593: 865, 14657: 897, 14753: 897, 15073: 897, 15137: 897, 15233: 897, 15329: 897,
    15361: 865, 15649: 897, 15809: 897, 15937: 897, 16001: 897, 16033: 897, 16097: 897,
    16193: 897, 16417: 897, 16481: 897, 16673: 897, 16993: 897, 17377: 897, 17569: 865,
    17729: 897, 17761: 865, 17921: 897, 18049: 897, 18401: 897, 18433: 865, 18593: 865,
    18913: 897, 19009: 897, 19073: 897, 19457: 897, 19489: 897, 19553: 897, 19681: 897,
    19777: 897, 19841: 865, 19937: 897,
}

# Spot prime above the scan range: (t=3 census maximum, t=4 below maximum, maximizers).
N32_SPOT = {65537: (4640, 897, ((16, 31), (17, 2)))}


def primes_one_mod(mod, limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start:limit + 1:divisor] = b"\x00" * len(sieve[start:limit + 1:divisor])
    return [p for p in range(mod, limit + 1) if sieve[p] and p % mod == 1]


def order_element(p, n):
    if (p - 1) % n:
        raise AssertionError(f"{n} does not divide p-1 for p={p}")
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def batch_inverse(values, p):
    """Invert a list mod p in O(len) multiplications; zeros map to zero."""
    count = len(values)
    prefix = [1] * (count + 1)
    for index, value in enumerate(values):
        prefix[index + 1] = prefix[index] * (value if value else 1) % p
    inverse = pow(prefix[count], -1, p)
    out = [0] * count
    for index in range(count - 1, -1, -1):
        value = values[index]
        if value:
            out[index] = inverse * prefix[index] % p
            inverse = inverse * value % p
    return out


def build(p, n):
    """Domain, per-exponent triple determinants, their inverses, and 4-subsets."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    powers = [[pow(x, exponent, p) for x in xs] for exponent in range(n)]
    triples = list(combinations(range(n), 3))
    triple_index = {triple: index for index, triple in enumerate(triples)}
    determinants = []
    for exponent in range(n):
        values = powers[exponent]
        row = [0] * len(triples)
        for index, (i, j, k) in enumerate(triples):
            dx1 = (xs[j] - xs[i]) % p
            dx2 = (xs[k] - xs[i]) % p
            dy1 = (values[j] - values[i]) % p
            dy2 = (values[k] - values[i]) % p
            row[index] = (dx1 * dy2 - dy1 * dx2) % p
        determinants.append(row)
    inverses = [batch_inverse(row, p) for row in determinants]
    quads = [
        (triple_index[(i, j, k)], triple_index[(i, j, l)])
        for i, j, k, l in combinations(range(n), 4)
    ]
    return xs, determinants, inverses, quads


def bad_sets(determinants, inverses, quads, a, b, p):
    """Return the exact t=3 and t=4 bad-scalar sets of the pencil (x^a, x^b)."""
    first = determinants[a]
    second = determinants[b]
    if b < 2:
        # x^0 and x^1 are affine on every witness, so the exclusion always fires.
        return set(), set()
    second_inverse = inverses[b]
    bad_ceiling = set()
    for index, db in enumerate(second):
        if db:
            bad_ceiling.add((-first[index] * second_inverse[index]) % p)
    bad_below = set()
    for base, fourth in quads:
        db = second[base]
        if db:
            gamma = (-first[base] * second_inverse[base]) % p
            if (first[fourth] + gamma * second[fourth]) % p == 0:
                bad_below.add(gamma)
        else:
            other = second[fourth]
            if other:
                gamma = (-first[fourth] * second_inverse[fourth]) % p
                if first[base] == 0:
                    bad_below.add(gamma)
    return bad_ceiling, bad_below


def char_pencils(n):
    """The four quadratic-character pencils (x^h, .) with h = n/2; all have odd exponent gap."""
    h = n // 2
    return ((h, h - 1), (h, n - 1), (h + 1, 2), (h + 1, h + 2))


def census(n, p):
    """Full monomial-pencil census at one prime; returns both threshold profiles."""
    xs, determinants, inverses, quads = build(p, n)
    counts_ceiling = {}
    counts_below = {}
    for a in range(n):
        for b in range(n):
            ceiling, below = bad_sets(determinants, inverses, quads, a, b, p)
            counts_ceiling[(a, b)] = len(ceiling)
            counts_below[(a, b)] = len(below)
    closed_form = {(-(xs[i] + xs[j] + xs[k])) % p for i, j, k in combinations(range(n), 3)}
    # The (x^3,x^2) ceiling stack is exactly the negated distinct three-sum spectrum.
    ceiling_32, _ = bad_sets(determinants, inverses, quads, 3, 2, p)
    assert ceiling_32 == closed_form, (n, p, len(ceiling_32), len(closed_form))
    # Odd exponent gap makes the bad set mu_n-invariant, so its size is
    # 1 (the fixed scalar 0) plus whole mu_n-orbits.
    for pair in char_pencils(n):
        _, bad = bad_sets(determinants, inverses, quads, pair[0], pair[1], p)
        assert len(bad) % n == (1 if 0 in bad else 0), (n, p, pair, len(bad))
    return xs, closed_form, counts_ceiling, counts_below


def summarize(counts):
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items() if count == maximum))
    return maximum, winners


def main():
    print("n=32 dimension-two below-ceiling monomial-pencil census (KKH26 rung)")
    print(f"t={T_CEIL} ceiling census and t={T_BELOW} below-ceiling census")

    # 1. Reproduce the published n=8 integers of G310/G328.
    for p in (17, 41, 257):
        _, closed_form, counts_ceiling, counts_below = census(8, p)
        ceiling_stack = counts_ceiling[(3, 2)]
        expected = 16 if p == 17 else 40
        assert ceiling_stack == len(closed_form) == expected, (p, ceiling_stack, expected)
        maximum, winners = summarize(counts_below)
        assert maximum == 9 and winners == G328_WINNERS, (p, maximum, winners)
        assert maximum <= GOOD_BOUND[8]
    print("n=8 reproduction: (x^3,x^2) t=3 count 40 (p=41,257) and 16 (p=17); "
          f"below-ceiling max 9 at {G328_WINNERS}")

    # 2. Reproduce the published n=16 integers of probe_n16_below_ceiling_max.py.
    for p, (expected_ceiling, expected_max, expected_winners) in N16_SPOT.items():
        _, closed_form, counts_ceiling, counts_below = census(16, p)
        assert counts_ceiling[(3, 2)] == expected_ceiling, (p, counts_ceiling[(3, 2)])
        maximum, winners = summarize(counts_below)
        assert maximum == expected_max, (p, maximum, expected_max)
        if expected_winners is not None:
            assert winners == expected_winners, (p, winners)
        assert maximum <= GOOD_BOUND[16]
        assert max(counts_below[(a, a)] for a in range(16)) <= 1
    print(f"n=16 reproduction: {len(N16_SPOT)} primes, including the 353 exception "
          "(81) and the two-element-tie primes")

    prize_p = 21 * (2 ** 128) + 1
    assert pow(5, (prize_p - 1) // 2, prize_p) == prize_p - 1
    _, _, counts_ceiling, counts_below = census(16, prize_p)
    assert counts_ceiling[(3, 2)] == 464
    assert summarize(counts_below) == (97, FOUR)
    print(f"n=16 prize-scale p = 21*2^128+1: (3,2) count 464, below max 97, {FOUR}")

    # 3. The new rung: every prime p = 1 (mod 32) in [97, LIMIT].
    primes = primes_one_mod(32, LIMIT)
    assert len(primes) == 146, len(primes)
    assert set(primes) == set(N32_T4), "profile does not cover the scanned primes"
    by_value = {}
    t3_maximum = {}
    t3_greater = 0
    t3_equal = 0
    for index, p in enumerate(primes):
        _, closed_form, counts_ceiling, counts_below = census(32, p)
        maximum, winners = summarize(counts_below)
        assert maximum == N32_T4[p], (p, maximum, N32_T4[p])
        assert maximum <= GOOD_BOUND[32], (p, maximum)
        assert max(counts_below[(a, a)] for a in range(32)) <= 1, p
        if maximum < p:
            assert set(winners) <= set(char_pencils(32)), (p, winners)
        by_value.setdefault(maximum, []).append(p)
        t3_top = summarize(counts_ceiling)[0]
        t3_maximum[p] = t3_top
        spectrum = len(closed_form)
        if t3_top > spectrum:
            t3_greater += 1
        elif t3_top == spectrum:
            t3_equal += 1
        if index % 25 == 0:
            print(f"  scanned {index + 1}/{len(primes)} primes (last p={p})", flush=True)

    assert t3_maximum[12289] == 4160, t3_maximum[12289]
    assert (t3_greater, t3_equal) == (116, 30), (t3_greater, t3_equal)
    print(f"n=32 scan: {len(primes)} primes p = 1 (mod 32) in [97, {LIMIT}]")
    print("t=4 below-ceiling maximum over all 1024 monomial pencils:")
    for value in sorted(by_value):
        plist = by_value[value]
        shown = str(plist) if len(plist) <= 16 else f"{plist[:16]} ... ({len(plist)} primes)"
        print(f"  {value}: {shown}")
    top = max(by_value)
    assert top == 897, top
    assert len(by_value[top]) == 70, len(by_value[top])
    print(f"  maximum {top} at {by_value[top]}")
    print("  every maximizer at a non-saturated prime is one of the four "
          f"quadratic-character pencils {char_pencils(32)}")
    print("  the t=3 census at (x^3,x^2) equals the negated three-sum spectrum at "
          f"every prime but is not the t=3 maximum at {t3_greater} of {len(primes)} "
          f"primes (equal at {t3_equal}); t=3 max at p=12289 is {t3_maximum[12289]}")

    # 3b. Spot prime above the scan range.
    for p, (expected_t3, expected_t4, expected_winners) in N32_SPOT.items():
        _, closed_form, counts_ceiling, counts_below = census(32, p)
        t3_top, _ = summarize(counts_ceiling)
        maximum, winners = summarize(counts_below)
        assert len(closed_form) == 3264, len(closed_form)
        assert t3_top == expected_t3, (p, t3_top, expected_t3)
        assert maximum == expected_t4, (p, maximum, expected_t4)
        assert winners == expected_winners, (p, winners)
        assert maximum <= GOOD_BOUND[32]
    print("n=32 spot p=65537: three-sum spectrum 3264, t=3 max 4640, t=4 below max "
          "897 at ((16,31),(17,2))")

    # 4. Prize-scale prime at the new rung.
    _, closed_form, counts_ceiling, counts_below = census(32, prize_p)
    t3_top, _ = summarize(counts_ceiling)
    maximum, winners = summarize(counts_below)
    assert len(closed_form) == 4512, len(closed_form)
    assert t3_top == 4640, t3_top
    assert maximum == 897 and winners == char_pencils(32), (maximum, winners)
    assert maximum <= GOOD_BOUND[32]
    print("n=32 prize-scale p = 21*2^128+1: (x^3,x^2) t=3 spectrum 4512, t=3 max "
          f"{t3_top}; t=4 below max {maximum}, maximizers {winners}")
    print("PASS: exact n=32 census on 146 primes plus the prize-scale prime; the "
          "n=8 and n=16 published integers are reproduced through a different "
          "collinearity algorithm; the four quadratic-character pencils carry "
          "every non-saturated maximizer")


if __name__ == "__main__":
    main()
