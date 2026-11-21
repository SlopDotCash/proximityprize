#!/usr/bin/env python3
"""Verify the integer bounds and small-field tests in production-ratio-lifting.md."""

from itertools import combinations
from math import isqrt


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def check_production():
    n = 2**30
    h = n // 4
    primes = (
        365375409332725729550921208179070755120141565953,
        730750818665451459101842416358141509841924915201,
    )
    require(all(p < 2**160 and (p - 1) % n == 0 for p in primes), "field size or splitting")
    s = 5_000_000
    pairs = (n - s) // 2
    degree = pairs // 2
    lower = pairs + degree - (pairs + 1).bit_length()
    require((pairs, degree, lower) == (534370912, 267185456, 801556339), "oriented supports")
    require(lower > 160 * (s - 1) == 799999840 and degree < h, "bounded degree collision")
    print(f"{s} sites: degree at most {degree}, exponents {lower} > {160 * (s - 1)}")

    s = 2**18
    require(27**4 > 8 * 16**4, "binomial estimate")
    for delta, q, padding, lower_bits in (
        (-1, 63700991, 781, 47775714),
        (1, 64749569, 777, 48562147),
    ):
        d = h + delta
        require(q > 1 and all(q % a for a in range(2, isqrt(q) + 1)), "auxiliary prime")
        require(4 * q <= h and (d - q) == s * padding, "support and padding")
        require(2 * (d - q) + s <= n // 2, "availability of distinct even cosets")
        lower = 3 * q // 4 - (2 * (4 * q + 1)).bit_length()
        require(lower == lower_bits and lower > 160 * (s - 1) == 41942880, "exact degree collision")
        require(3 * n // 8 + 6 <= 2 * d - 2, "all-translation test")
        print(f"{s} sites: exact degree {d}, exponents {lower} > {160 * (s - 1)}, padding {padding}")


def check_full_fiber():
    n = 2**30
    h = n // 4
    p = 365375409332725729550921208179070755120141565953
    require(p > 12 * n**4, "positive-characteristic correction")
    for d, t in ((h - 1, h - 1), (h + 1, h + 1), (h, h - 1)):
        points = d + 2 * t
        coarse = (points**3 + 108 * n**2 - 1) // (108 * n**2)
        threshold = (13 * points - 7 * n + 324) // 325
        require(coarse > 8 and threshold == 9085508, "component degree")
        require(d // (threshold + 1) == 29, "outer degree cap")
        print(f"degree {d}, protected {t}: orbital degree at least {threshold}")
    require([i for i in range(2, 30) if (h - 1) % i == 0] == [3, 5, 15, 29],
            "predecessor outer degrees")
    require([i for i in range(2, 30) if (h + 1) % i == 0] == [17], "successor outer degree")
    require(h - 1 == 3 * 5 * 29 * 43 * 113 * 127 and h + 1 == 17 * 15790321,
            "odd-degree factorizations")
    require(all(15790321 % a for a in range(2, isqrt(15790321) + 1)), "large prime factor")


def rotate(mask, shift, n):
    return ((mask << shift) | (mask >> (n - shift))) & ((1 << n) - 1)


def check_translated_ratios(n, p, degrees):
    generator = next(g for g in range(1, p) if pow(g, n, p) == 1 and pow(g, n // 2, p) != 1)
    sites = [pow(generator, i, p) for i in range(n)]
    tested = 0
    for d in degrees:
        values = {}
        for support in combinations(range(n), d):
            mask = sum(1 << i for i in support)
            row = []
            for x in sites:
                y = 1
                for i in support:
                    y = y * (x - sites[i]) % p
                row.append(y)
            values[mask] = row
        for a, numerator in values.items():
            for b, denominator in values.items():
                if b <= a or a & b:
                    continue
                fibers = {}
                for i in range(n):
                    if (a | b) >> i & 1:
                        continue
                    v = numerator[i] * pow(denominator[i], -1, p) % p
                    fibers[v] = fibers.get(v, 0) | (1 << i)
                for j in range(1, n):
                    aj, bj = rotate(a, j, n), rotate(b, j, n)
                    if a == aj and b == bj:
                        continue
                    reduced_degree = 2 * d - (a & aj).bit_count() - (b & bj).bit_count()
                    for t in fibers.values():
                        require((t & rotate(t, j, n)).bit_count() <= reduced_degree - 2,
                                "translated-ratio bound")
                        tested += 1
    print(f"order {n} in F_{p}: {tested} translated proper-fiber checks")


def check_trace_coloring(modulus):
    """Use a primitive binary polynomial, then take the trace down to F4."""
    n = 1 << (modulus.bit_length() - 1)
    powers = []
    x = 1
    for _ in range(n - 1):
        powers.append(x)
        x <<= 1
        if x & n:
            x ^= modulus
    require(len(set(powers)) == n - 1 and x == 1, "primitive polynomial")
    colors = []
    for i in range(n - 1):
        value = 0
        for j in range((n.bit_length() - 1) // 2):
            value ^= powers[(i * 4**j) % (n - 1)]
        colors.append(value)
    colors.append(0)
    nonzero = set(colors) - {0}
    require(len(nonzero) == 3 and all(colors.count(c) == n // 4 for c in nonzero), "F4 colors")
    same = [sum(v != 0 and v == colors[(i + j) % n] for i, v in enumerate(colors))
            for j in range(1, n)]
    require(max(same) <= 3 * n // 8, "cyclic autocorrelations")
    print(f"order {n}: trace colors have maximum nonidentity autocorrelation {max(same)}")


if __name__ == "__main__":
    check_production()
    check_full_fiber()
    check_translated_ratios(8, 17, (1, 2, 3))
    check_translated_ratios(8, 41, (1, 2, 3))
    check_translated_ratios(16, 97, (2,))
    for primitive in (0x13, 0x43, 0x11D):
        check_trace_coloring(primitive)
