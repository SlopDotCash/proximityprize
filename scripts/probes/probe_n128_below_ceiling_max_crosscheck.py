#!/usr/bin/env python3
"""Independent re-computation of the n=128 below-ceiling census claims.

This file deliberately shares no counting code with
``probe_n128_below_ceiling_max.py``.  It re-derives the integers through two
separate devices:

1. A *literal* MCA event at ``n = 8``: for every scalar ``gamma`` in ``F_p``,
   every pencil and every 3- or 4-subset, decide collinearity by the secant
   slope test, and check the ``pairJointAgreesOn`` exclusion directly.  No
   determinants, no divided differences, no coset decomposition.  This pins
   the semantics of the event itself.

2. A direct determinant census.  For a pencil ``(a,b)`` it builds the
   collinearity determinants ``D_e(T)`` on every triple and enumerates every
   4-subset explicitly; the bad gamma of a 4-subset is read off two triples
   that share two points.  This engine reproduces the published anchors at
   n=16 and n=32 over *all* pencils, and at n=128 it re-computes the four
   maximizers at three prize-scale primes, the five highest distinct t=4
   values printed by the main probe, and a fixed 30-pencil sample.

Expected values are the integers printed by
``probe_n128_below_ceiling_max.py``; a ``None`` entry means the main probe
skipped that pencil at the t=3 upper-bound filter, so the direct engine must
confirm ``t4 < 63489`` there instead of an exact value.

Scope: same as the main probe -- finite fields, ``mu_128``, dimension-two
affine code, monomial pencils only, no production or ``delta*`` claim.
Stdlib only, deterministic, integer arithmetic only.
"""

import sys
from itertools import combinations
from math import gcd

PRIZE_EXP = 128
PRIZE_K = 21
EXTRA_PRIZE = ((111, 5), (123, 7))

CHAR_T3 = 67585
CHAR_T4 = 63489
N16_T4 = 97
N32_T4 = 897
N64_T4 = 7681
N8_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))

TOP = {
    (64, 63): 63489,
    (2, 65): 63488,
    (32, 31): 17409,
    (31, 32): 17408,
    (32, 63): 15361,
}

SAMPLE = {
    (0, 0): None,
    (7, 27): 800,
    (8, 104): None,
    (16, 80): None,
    (17, 29): 449,
    (24, 56): None,
    (25, 5): 481,
    (33, 109): 385,
    (34, 58): 496,
    (41, 85): 481,
    (42, 34): 496,
    (50, 10): 496,
    (51, 87): 992,
    (58, 114): 496,
    (59, 63): 992,
    (67, 39): 992,
    (68, 116): None,
    (75, 15): 992,
    (76, 92): None,
    (84, 68): None,
    (85, 17): 448,
    (92, 44): None,
    (93, 121): 480,
    (101, 97): 384,
    (102, 46): 496,
    (109, 73): 480,
    (110, 22): 496,
    (118, 126): 496,
    (119, 75): 544,
    (127, 51): 928,
}


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
    prefix = [1] * (len(values) + 1)
    for index, value in enumerate(values):
        prefix[index + 1] = prefix[index] * (value if value else 1) % p
    inverse = pow(prefix[-1], -1, p)
    out = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        value = values[index]
        if value:
            out[index] = inverse * prefix[index] % p
            inverse = inverse * value % p
    return out


def char_pencils(n):
    h = n // 2
    return ((h, h - 1), (h, n - 1), (h + 1, 2), (h + 1, h + 2))


def collinear(xs, values, subset, p):
    i, j = subset[0], subset[1]
    dx = (xs[j] - xs[i]) % p
    dy = (values[j] - values[i]) % p
    for other in subset[2:]:
        if ((xs[other] - xs[i]) * dy - (values[other] - values[i]) * dx) % p:
            return False
    return True


def literal_bad_set(n, p, a, b, size):
    """Direct event: every gamma, every `size`-subset, secant-slope test."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    u0 = [pow(x, a, p) for x in xs]
    u1 = [pow(x, b, p) for x in xs]
    subsets = list(combinations(range(n), size))
    bad = set()
    for gamma in range(p):
        values = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
        for subset in subsets:
            if collinear(xs, values, subset, p):
                if not (collinear(xs, u0, subset, p)
                        and collinear(xs, u1, subset, p)):
                    bad.add(gamma)
                    break
    return bad


def direct_counts(n, p, a, b):
    """Direct determinant census of the ceiling and below-ceiling bad sets."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    triples = list(combinations(range(n), 3))
    triple_index = {triple: index for index, triple in enumerate(triples)}
    det = {}
    for exponent in (a, b):
        word = [pow(x, exponent, p) for x in xs]
        det[exponent] = [
            ((xs[j] - xs[i]) * (word[k] - word[i])
             - (xs[k] - xs[i]) * (word[j] - word[i])) % p
            for i, j, k in triples
        ]
    first, second = det[a], det[b]
    inverse = batch_inverse(second, p)
    ratio = [first[t] * inverse[t] % p if second[t] else None
             for t in range(len(second))]
    ceiling = set()
    add = ceiling.add
    for value in ratio:
        if value is not None:
            add((-value) % p)
    below = set()
    add_below = below.add
    for i, j, k, l in combinations(range(n), 4):
        base = triple_index[(i, j, k)]
        fourth = triple_index[(i, j, l)]
        rb = ratio[base]
        if rb is not None:
            rf = ratio[fourth]
            if rf is None:
                if first[fourth] == 0:
                    add_below((-rb) % p)
            elif rb == rf:
                add_below((-rb) % p)
        else:
            rf = ratio[fourth]
            if rf is not None and first[base] == 0:
                add_below((-rf) % p)
    m = n // gcd((b - a) % n, n)
    zero = 0 in below
    assert (len(below) - (1 if zero else 0)) % m == 0, (n, a, b, len(below), m)
    return len(ceiling), len(below)


def all_pencil_matrix(n, p):
    """Direct census over all n^2 pencils; returns the counts matrix."""
    counts = {}
    for a in range(n):
        for b in range(n):
            counts[(a, b)] = direct_counts(n, p, a, b)[1]
    return counts


def summarize(counts):
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items()
                           if count == maximum))
    return maximum, winners


def main():
    prize = PRIZE_K * (2 ** PRIZE_EXP) + 1
    assert pow(5, (prize - 1) // 2, prize) == prize - 1
    print(f"independent re-computation; prize-scale p = {prize}", flush=True)

    # 1. Literal event at n=8 over every scalar and every subset.
    for p in (17, 41, 257):
        counts = {}
        for a in range(8):
            for b in range(8):
                counts[(a, b)] = len(literal_bad_set(8, p, a, b, 4))
                if (a, b) == (3, 2):
                    expected = 16 if p == 17 else 40
                    assert len(literal_bad_set(8, p, a, b, 3)) == expected, p
        assert summarize(counts) == (9, N8_WINNERS), (p, summarize(counts))
    print("literal n=8 event PASS: (3,2) t=3 16/40, t=4 max 9 at the four "
          "G328 winners", flush=True)

    # 2. Direct censuses of all pencils at n = 16 and n = 32.
    for n, expected, winners_expected in (
        (16, N16_T4, char_pencils(16)),
        (32, N32_T4, char_pencils(32)),
    ):
        counts = all_pencil_matrix(n, prize)
        assert summarize(counts) == (expected, winners_expected), (n, summarize(counts))
        print(f"direct n={n} census PASS: t=4 max {expected} at "
              f"{winners_expected}", flush=True)

    # 3. Direct character-pencil runs at n = 64 (all four).
    for a, b in char_pencils(64):
        assert direct_counts(64, prize, a, b)[1] == N64_T4, (a, b)
    print("direct n=64 character pencils PASS: t=4 7681", flush=True)

    # 4. n=128 character pencils at the three prize-scale primes.
    for k, witness in ((PRIZE_K, 5),) + EXTRA_PRIZE:
        p = k * (2 ** PRIZE_EXP) + 1
        assert pow(witness, (p - 1) // 2, p) == p - 1, k
        for a, b in char_pencils(128):
            t3, t4 = direct_counts(128, p, a, b)
            assert (t3, t4) == (CHAR_T3, CHAR_T4), (k, a, b, t3, t4)
        print(f"direct n=128 character pencils at p = {k}*2^128+1 PASS: "
              f"t=3 {CHAR_T3}, t=4 {CHAR_T4}", flush=True)

    # 5. Direct re-computation of the five highest distinct t=4 values.
    for (a, b), expected in TOP.items():
        t4 = direct_counts(128, prize, a, b)[1]
        assert t4 == expected, (a, b, t4, expected)
    print(f"direct top-5 PASS: {sorted(TOP.items(), key=lambda kv: -kv[1])}",
          flush=True)

    # 6. Direct re-computation of the fixed 30-pencil sample.
    for (a, b), expected in SAMPLE.items():
        t4 = direct_counts(128, prize, a, b)[1]
        if expected is None:
            assert t4 < CHAR_T4, (a, b, t4)
        else:
            assert t4 == expected, (a, b, t4, expected)
    print(f"direct 30-pencil sample PASS: exact values match, and all "
          f"{sum(1 for v in SAMPLE.values() if v is None)} filter-skipped "
          f"pencils have t4 < {CHAR_T4}", flush=True)
    print("PASS: independent devices agree with the main probe", flush=True)


if __name__ == "__main__":
    sys.exit(main())
