#!/usr/bin/env python3
"""Independent cross-check for ``probe_n32_below_ceiling_max.py``.

The main probe decides badness with precomputed per-exponent collinearity
determinants and a single cross-multiplication per 4-subset.  This script uses
different algorithms:

* bad scalars are sampled from explicit 2x2 Cramer elimination on every triple,
  then decided by grouping the C(n,2) pair lines of the candidate and auditing
  the *full* line witness with direct affine tests (the literal MCA event);
* a literal checker enumerates every witness subset for tiny rungs, and every
  ``t``-subset over the whole field for two n = 32 spot pencils;
* the n = 8 and n = 16 published integers are recomputed from scratch with the
  line-witness algorithm, without reusing any main-probe counting code.

Stdlib only, exact integer arithmetic, no floats, hard asserts.
"""

import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_n32_below_ceiling_max as main_probe  # noqa: E402


def order_element(p, n):
    if (p - 1) % n:
        raise AssertionError(f"{n} does not divide p-1 for p={p}")
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def affine_test(values, points, xs, p):
    """Affinity test by cross-multiplication, no field inverses."""
    if len(points) <= 2:
        return True
    i, j = points[0], points[1]
    dx = (xs[j] - xs[i]) % p
    dy = (values[j] - values[i]) % p
    for index in points[2:]:
        if (dx * (values[index] - values[i]) - (xs[index] - xs[i]) * dy) % p:
            return False
    return True


def bad_set_lines(n, xs, u0, u1, threshold, p):
    """Literal line-witness algorithm: candidates from triples, full-line audit."""
    pair_inverse = {
        (i, j): pow((xs[j] - xs[i]) % p, -1, p) for i, j in combinations(range(n), 2)
    }
    candidates = set()
    for i, j, k in combinations(range(n), 3):
        a11 = (u1[j] - u1[i]) % p
        a12 = (xs[i] - xs[j]) % p
        a21 = (u1[k] - u1[i]) % p
        a22 = (xs[i] - xs[k]) % p
        determinant = (a11 * a22 - a12 * a21) % p
        if not determinant:
            continue
        b1 = (u0[j] - u0[i]) % p
        b2 = (u0[k] - u0[i]) % p
        gamma = ((-b1) * a22 - a12 * (-b2)) * pow(determinant, -1, p) % p
        candidates.add(gamma)
    min_pairs = threshold * (threshold - 1) // 2
    bad = set()
    for gamma in candidates:
        pencil = [(u0[index] + gamma * u1[index]) % p for index in range(n)]
        lines = {}
        for i, j in combinations(range(n), 2):
            slope = (pencil[j] - pencil[i]) * pair_inverse[(i, j)] % p
            intercept = (pencil[i] - slope * xs[i]) % p
            lines.setdefault((slope, intercept), []).append(i)
        for (slope, intercept), indices in lines.items():
            if len(indices) < min_pairs:
                continue
            witness = [
                index for index in range(n)
                if (intercept + slope * xs[index] - pencil[index]) % p == 0
            ]
            if len(witness) < threshold:
                continue
            if not (affine_test(u0, witness, xs, p) and affine_test(u1, witness, xs, p)):
                bad.add(gamma)
                break
    return bad


def bad_set_literal(n, xs, u0, u1, threshold, p):
    """Literal MCA definition: enumerate every witness subset of size >= threshold."""
    bad = set()
    for gamma in range(p):
        pencil = [(u0[index] + gamma * u1[index]) % p for index in range(n)]
        is_bad = False
        for size in range(threshold, n + 1):
            for points in combinations(range(n), size):
                if not affine_test(pencil, points, xs, p):
                    continue
                if not (affine_test(u0, points, xs, p) and affine_test(u1, points, xs, p)):
                    is_bad = True
                    break
            if is_bad:
                break
        if is_bad:
            bad.add(gamma)
    return bad


def values(xs, a, b, p):
    return [pow(x, a, p) for x in xs], [pow(x, b, p) for x in xs]


def slow_census(n, p):
    xs = [pow(order_element(p, n), exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    counts_ceiling = {}
    counts_below = {}
    for a in range(n):
        for b in range(n):
            u0, u1 = values(xs, a, b, p)
            counts_ceiling[(a, b)] = len(bad_set_lines(n, xs, u0, u1, 3, p))
            counts_below[(a, b)] = len(bad_set_lines(n, xs, u0, u1, 4, p))
    return xs, counts_ceiling, counts_below


def summarize(counts):
    maximum = max(counts.values())
    return maximum, tuple(sorted(pair for pair, count in counts.items() if count == maximum))


def main():
    print("independent cross-check for the n=32 below-ceiling census")

    # 1. Literal-definition equivalence at n = 8 (every witness subset, every gamma).
    for p in (17, 41):
        xs = [pow(order_element(p, 8), exponent, p) for exponent in range(8)]
        for a in range(8):
            for b in range(8):
                u0, u1 = values(xs, a, b, p)
                for threshold in (3, 4):
                    literal = bad_set_literal(8, xs, u0, u1, threshold, p)
                    linewise = bad_set_lines(8, xs, u0, u1, threshold, p)
                    assert literal == linewise, (p, a, b, threshold)
    print("n=8: literal all-subset MCA definition == line-witness algorithm on all 64 pencils")

    # 2. Main probe == line-witness algorithm at n = 8, all 64 pencils.
    for p in (17, 41, 257):
        xs, determinants, inverses, quads = main_probe.build(p, 8)
        for a in range(8):
            for b in range(8):
                fast_ceiling, fast_below = main_probe.bad_sets(determinants, inverses, quads, a, b, p)
                u0, u1 = values(xs, a, b, p)
                assert fast_ceiling == bad_set_lines(8, xs, u0, u1, 3, p), (p, a, b, 3)
                assert fast_below == bad_set_lines(8, xs, u0, u1, 4, p), (p, a, b, 4)
    print("n=8: main probe == line-witness algorithm on all 64 pencils at p=17,41,257")

    # 3. Published n=8 / n=16 integers, recomputed by the line-witness algorithm.
    for p in (17, 41, 257):
        _, counts_ceiling, counts_below = slow_census(8, p)
        maximum, winners = summarize(counts_below)
        ceiling = counts_ceiling[(3, 2)]
        assert maximum == 9 and winners == main_probe.G328_WINNERS, (p, maximum, winners)
        assert ceiling == (16 if p == 17 else 40), (p, ceiling)
    print("n=8 published integers reproduced: ceiling 40/16, below max 9, G328 maximizers")

    prize_p = 21 * (2 ** 128) + 1
    assert pow(5, (prize_p - 1) // 2, prize_p) == prize_p - 1
    n16_expected = {
        97: (96, 97, ((8, 15), (9, 2))),
        353: (272, 81, main_probe.FOUR),
        12289: (464, 97, main_probe.FOUR),
        19489: (464, 97, main_probe.FOUR),
        65537: (464, 97, main_probe.FOUR),
    }
    for p, expected in n16_expected.items():
        _, counts_ceiling, counts_below = slow_census(16, p)
        observed = (counts_ceiling[(3, 2)], *summarize(counts_below))
        assert observed == expected, (p, observed, expected)
    _, counts_ceiling, counts_below = slow_census(16, prize_p)
    assert (counts_ceiling[(3, 2)], *summarize(counts_below)) == (464, 97, main_probe.FOUR)
    print("n=16 published integers reproduced at p=97,353,12289,19489,65537 and 21*2^128+1")

    # 4. n=32: slow == fast on the maximizer family and a deterministic sample,
    #    with full bad-set equality (not only counts).
    sample = [(3, 2), (0, 0), (0, 5), (1, 5), (5, 4), (7, 30), (16, 15), (16, 31),
              (17, 2), (17, 18), (25, 26), (31, 31)]
    for p in (577, 2593, 4801, 12289, 65537):
        xs, determinants, inverses, quads = main_probe.build(p, 32)
        assert main_probe.bad_sets(determinants, inverses, quads, 3, 2, p)[0] == {
            (-(xs[i] + xs[j] + xs[k])) % p for i, j, k in combinations(range(32), 3)
        }
        for a, b in sample:
            u0, u1 = values(xs, a, b, p)
            fast_ceiling, fast_below = main_probe.bad_sets(determinants, inverses, quads, a, b, p)
            assert fast_ceiling == bad_set_lines(32, xs, u0, u1, 3, p), (p, a, b, 3)
            assert fast_below == bad_set_lines(32, xs, u0, u1, 4, p), (p, a, b, 4)
    print("n=32: main probe == line-witness algorithm on 12 pencils at 5 primes "
          "(ceiling and below sets identical)")

    # 5. Literal t-subset enumeration over the whole field at n = 32, p = 97.
    p = 97
    xs = [pow(order_element(p, 32), exponent, p) for exponent in range(32)]
    determinants, inverses, quads = main_probe.build(p, 32)[1:]
    for (a, b), threshold in (((3, 2), 3), ((16, 31), 4)):
        u0, u1 = values(xs, a, b, p)
        literal = set()
        for gamma in range(p):
            pencil = [(u0[index] + gamma * u1[index]) % p for index in range(32)]
            for points in combinations(range(32), threshold):
                if not affine_test(pencil, points, xs, p):
                    continue
                if not (affine_test(u0, points, xs, p) and affine_test(u1, points, xs, p)):
                    literal.add(gamma)
                    break
        fast_ceiling, fast_below = main_probe.bad_sets(determinants, inverses, quads, a, b, p)
        fast_set = fast_ceiling if threshold == 3 else fast_below
        assert fast_set == literal, (a, b, threshold, len(fast_set), len(literal))
        print(f"  literal p=97 pencil {(a, b)} t={threshold}: {len(literal)} bad scalars")

    print("PASS: every asserted integer and every bad-scalar set agrees between the "
          "main probe, the line-witness algorithm and the literal MCA definition")


if __name__ == "__main__":
    main()
