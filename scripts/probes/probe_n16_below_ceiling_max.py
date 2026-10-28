#!/usr/bin/env python3
"""Exact n=16 dimension-two below-ceiling monomial-pencil census.

Reproduces the order-eight (n = 8) integers of G310/G328 and computes the next
rung n = 16 on the order-sixteen subgroup mu_16:

* the ceiling stack (x^3, x^2) at agreement threshold t = 3, whose bad-scalar
  set is the negated signed weight-{1,3} subset-sum spectrum of KKH26
  (2*C(8,1) + 2^3*C(8,3) = 464 data before collisions);
* the maximum bad-scalar count over all monomial pencils (x^a, x^b),
  0 <= a, b < 16, at the below-ceiling threshold t = 4.

Semantics: the integer-threshold MCA event of
``g328_k2_field_stability_boundary.py``, including the ``pairJointAgreesOn``
exclusion (a scalar is bad only if some witness set of size >= t is affine on
neither row jointly).

Everything is exact integer arithmetic; no floats appear in any load-bearing
value.  Stdlib only, deterministic, and every printed claim is hard-asserted.

Scope (read before citing): finite fields only, fixed small rungs n = 8 and
n = 16, monomial pencils only.  The scan range is [17, 20000] plus one
prize-scale Proth prime.  This is not a field-uniform theorem, not a maximum
over all stacks, not a production n = 2^30/2^32 statement, and not a claim
about delta* or the prize.
"""

from itertools import combinations
from math import isqrt

N8 = 8
N16 = 16
T_CEIL = 3
T_BELOW = 4
LIMIT = 20_000

FOUR = ((8, 7), (8, 15), (9, 2), (9, 10))
G328_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))

# The n=16 ceiling count (x^3,x^2) at t=3 is 464 outside the 34-prime
# exceptional set computed by the signed-spectrum route (PR #264).
CEILING_EXCEPTIONS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}

# Below-ceiling maxima that differ from 97.
BELOW_EXCEPTIONS = {17: 17, 353: 81}

# Primes where the max is 97 but only two of the four generic maximizers tie.
BELOW_TWO_WINNERS = {
    97: ((8, 15), (9, 2)),
    113: ((8, 7), (9, 10)),
    241: ((8, 15), (9, 2)),
    257: ((8, 15), (9, 2)),
    449: ((8, 15), (9, 2)),
    1217: ((8, 15), (9, 2)),
}

# Explicit n=16 spot values: (ceiling count, below-ceiling max, maximizers).
SPOT = {
    17: (17, 17),
    97: (96, 97, ((8, 15), (9, 2))),
    113: (112, 97, ((8, 7), (9, 10))),
    241: (240, 97, ((8, 15), (9, 2))),
    257: (224, 97, ((8, 15), (9, 2))),
    353: (272, 81, FOUR),
    449: (336, 97, ((8, 15), (9, 2))),
    1201: (464, 97, FOUR),
    1217: (448, 97, ((8, 15), (9, 2))),
    12289: (464, 97, FOUR),
    19489: (464, 97, FOUR),
    65537: (464, 97, FOUR),
}


def primes_one_mod(p_mod, limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start:limit + 1:divisor] = b"\x00" * len(sieve[start:limit + 1:divisor])
    return [p for p in range(p_mod, limit + 1) if sieve[p] and p % p_mod == 1]


def order_element(p, n):
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def affine_on(values, points, xs, p):
    if len(points) <= 2:
        return True
    first, second = points[0], points[1]
    slope = (values[second] - values[first]) * pow((xs[second] - xs[first]) % p, -1, p) % p
    intercept = (values[first] - slope * xs[first]) % p
    return all((intercept + slope * xs[index] - values[index]) % p == 0 for index in points)


def pencil_context(n, xs, powers, p):
    """Pair inverses and per-exponent triple elimination data, shared by all pencils."""
    pair_inv = {
        (i, j): pow((xs[j] - xs[i]) % p, -1, p)
        for i, j in combinations(range(n), 2)
    }
    triple_data = {}
    for exponent in range(n):
        u = powers[exponent]
        data = {}
        for i, j, k in combinations(range(n), 3):
            a11 = (u[j] - u[i]) % p
            a12 = (xs[i] - xs[j]) % p
            a21 = (u[k] - u[i]) % p
            a22 = (xs[i] - xs[k]) % p
            det = (a11 * a22 - a12 * a21) % p
            if det:
                data[(i, j, k)] = (a11, a12, a21, a22, pow(det, -1, p))
        triple_data[exponent] = data
    return pair_inv, triple_data


def bad_scalars(n, xs, powers, pair_inv, triple_data, first, second, threshold, p):
    """Scalars gamma with a t-point affine-compliance witness that is not jointly affine."""
    u0 = powers[first]
    u1 = powers[second]
    candidates = set()
    for (i, j, k), (a11, a12, a21, a22, det_inv) in triple_data[second].items():
        b1 = (u0[j] - u0[i]) % p
        b2 = (u0[k] - u0[i]) % p
        candidates.add((((-b1) * a22) - (a12 * (-b2))) % p * det_inv % p)

    min_pairs = threshold * (threshold - 1) // 2
    bad = set()
    for gamma in candidates:
        values = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
        lines = {}
        for i, j in combinations(range(n), 2):
            slope = (values[j] - values[i]) * pair_inv[(i, j)] % p
            intercept = (values[i] - slope * xs[i]) % p
            lines.setdefault((slope, intercept), []).append((i, j))
        for (slope, intercept), pairs in lines.items():
            if len(pairs) < min_pairs:
                continue
            witness = [
                index for index in range(n)
                if (intercept + slope * xs[index] - values[index]) % p == 0
            ]
            if len(witness) < threshold:
                continue
            if not (affine_on(u0, witness, xs, p) and affine_on(u1, witness, xs, p)):
                bad.add(gamma)
                break
    return bad


def ceiling_triple_sums(n, xs, p):
    """Closed form for the (x^3,x^2) t=3 bad set: negatives of distinct 3-sums."""
    return {(-(xs[i] + xs[j] + xs[k])) % p for i, j, k in combinations(range(n), 3)}


def census(n, p):
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    powers = [[pow(x, exponent, p) for x in xs] for exponent in range(n)]
    pair_inv, triple_data = pencil_context(n, xs, powers, p)
    ceiling = bad_scalars(n, xs, powers, pair_inv, triple_data, 3, 2, T_CEIL, p)
    counts = {}
    for first in range(n):
        for second in range(n):
            counts[(first, second)] = len(
                bad_scalars(n, xs, powers, pair_inv, triple_data,
                            first, second, T_BELOW, p)
            )
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items() if count == maximum))
    diagonal_max = max(counts[(a, a)] for a in range(n))
    return xs, ceiling, maximum, winners, diagonal_max


def check_spectrum_closed_form(n, xs, ceiling, p):
    direct = ceiling_triple_sums(n, xs, p)
    assert ceiling == direct, (p, len(ceiling), len(direct))


def main():
    print("n=16 dimension-two below-ceiling monomial-pencil census")

    # 1. Reproduce the order-eight G310/G328 integers.
    for p in (17, 41, 257):
        xs, ceiling, maximum, winners, diagonal_max = census(N8, p)
        check_spectrum_closed_form(N8, xs, ceiling, p)
        expected_ceiling = 16 if p == 17 else 40
        assert len(ceiling) == expected_ceiling, (p, len(ceiling))
        assert maximum == 9 and winners == G328_WINNERS, (p, maximum, winners)
    print("n=8 reproduction: ceiling 40 (p=41,257) and 16 (p=17); "
          f"below-ceiling max 9 at {G328_WINNERS}")

    # 2. Explicit n=16 spot checks (including the prize-scale prime).
    for p, (expected_ceiling, expected_max, *rest) in SPOT.items():
        xs, ceiling, maximum, winners, diagonal_max = census(N16, p)
        check_spectrum_closed_form(N16, xs, ceiling, p)
        assert len(ceiling) == expected_ceiling, (p, len(ceiling), expected_ceiling)
        assert maximum == expected_max, (p, maximum, expected_max)
        if rest:
            assert winners == rest[0], (p, winners)
        if p >= 1201:
            assert diagonal_max <= 1, (p, diagonal_max)

    prize_exp = 128
    prize_k = 21
    prize_p = prize_k * (2 ** prize_exp) + 1
    assert prize_k % 2 == 1 and prize_k < 2 ** prize_exp
    assert pow(5, (prize_p - 1) // 2, prize_p) == prize_p - 1
    xs, ceiling, maximum, winners, diagonal_max = census(N16, prize_p)
    check_spectrum_closed_form(N16, xs, ceiling, prize_p)
    assert len(ceiling) == 464 and maximum == 97 and winners == FOUR
    assert diagonal_max <= 1
    print(f"n=16 spot checks pass (incl. prize-scale p = 21*2^128+1: "
          f"ceiling 464, below max 97, maximizers {FOUR})")

    # 3. Full scan over every prime p = 1 (mod 16) in [17, LIMIT].
    primes = primes_one_mod(16, LIMIT)
    assert primes[0] == 17 and len(primes) == 279
    ceiling_profile = {}
    below_profile = {}
    for index, p in enumerate(primes):
        xs, ceiling, maximum, winners, diagonal_max = census(N16, p)
        assert diagonal_max <= 1, (p, diagonal_max)
        ceiling_profile[p] = len(ceiling)
        below_profile[p] = (maximum, winners)
        if index % 25 == 0:
            print(f"  scanned {index + 1}/{len(primes)} primes (last p={p})", flush=True)

    for p in primes:
        assert ceiling_profile[p] == CEILING_EXCEPTIONS.get(p, 464), (p, ceiling_profile[p])
        maximum, winners = below_profile[p]
        assert maximum == BELOW_EXCEPTIONS.get(p, 97), (p, maximum)
        if p != 17:
            expected = BELOW_TWO_WINNERS.get(p, FOUR)
            assert winners == expected, (p, winners)

    ceiling_split = sorted((p, c) for p, c in ceiling_profile.items() if c != 464)
    below_split = sorted((p, c) for p, c in below_profile.items() if c[0] != 97)
    assert [p for p, _ in ceiling_split] == sorted(CEILING_EXCEPTIONS)
    assert len(below_split) == 2
    print(f"scan: {len(primes)} primes p = 1 (mod 16) in [17, {LIMIT}]")
    print(f"ceiling (x^3,x^2) t=3: 464 outside the {len(ceiling_split)}-prime set "
          f"{[p for p, _ in ceiling_split]}")
    print(f"below-ceiling t=4 max: 97 at 277 primes; exceptions {below_split[0][0]}:"
          f"{below_split[0][1][0]} and {below_split[1][0]}:{below_split[1][1][0]}")
    print(f"maximizers: {FOUR} except {sorted(BELOW_TWO_WINNERS)} (two-element ties)")
    print("PASS: n=16 below-ceiling maximum is 97 on the scanned range and at the "
          "prize-scale Proth prime")


if __name__ == "__main__":
    main()
