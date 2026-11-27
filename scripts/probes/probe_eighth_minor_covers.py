#!/usr/bin/env python3
"""Exact arithmetic for the second-prime eighth-rate projective minor cover obstruction."""
from math import isqrt

N = 2**30
D = N // 8 - 1
P2 = N * (2**129 + 13) + 1
EXPECTED = {
    1: [(22_369_621, 12), (44_739_242, 6), (67_108_863, 4), (134_217_726, 2)],
    2: [(5_368_709, 50), (26_843_545, 10), (134_217_725, 2)],
    3: [(4_329_604, 62), (33_554_431, 8), (67_108_862, 4), (134_217_724, 2)],
    4: [(3_273_603, 82), (44_739_241, 6), (134_217_723, 2)],
}


def check(condition, claim):
    if not condition:
        raise ValueError(claim)


def ceil_div(a, b):
    return -(-a // b)


def divisors(x):
    return sorted({v for i in range(1, isqrt(x) + 1) if x % i == 0 for v in (i, x // i)})


def verify():
    # Check all owner masks. For fixed common order g the four terms are minimized
    # independently by taking max(g, required face order).
    for mask in range(16):
        owners = mask.bit_count()
        orders = [max(0, owners - ((mask >> i) & 1) - 1) for i in range(4)]
        for g in range(12):
            total = sum(max(g, x) for x in orders)
            check(g + 2 * max(0, owners - 1) <= total, "local common-order charge")
    # All possible small exceptional strata, independently of their polynomial provenance.
    for s in range(5):
        for x0 in range(s + 1):
            for x3 in range(2 * s + 1):
                for x4 in range(s + 1):
                    if 2 * x0 + x3 + 2 * x4 > 2 * s:
                        continue
                    x2 = 4 * D + x0 - s - 2 * x3 - 3 * x4
                    check(x2 >= 4 * D - 5 * s, "double sites")
                    for base in range(2 * s + 1):
                        e = x2 - base
                        capacity = 4 * D - 2 * base
                        check(capacity - e <= 5 * s - base, "aggregate missing sheets")
                        check(2 * e - capacity >= 4 * D - 10 * s, "protected pairs per valency")
    check(12 * N**2 * (2 * D)**2 < P2 and 18 * N * (2 * D) < P2, "characteristic")
    protected = 4 * D - 40
    cubic = ceil_div(protected**3, 108 * N**2)
    linear = ceil_div(74 * protected - 26 * N, 74 * 73)
    check((protected, cubic, linear) == (536_870_868, 1_242_757, 2_186_442), "curve thresholds")
    check(cubic > 4 * 14, "coordinate degrees after quotient by the torus stabilizer")
    check(protected > 3_143_679, "non-dihedral deck bound")

    # Pure arithmetic behind the syzygy remainder condition, including odd outside degrees.
    for d in range(1, 96):
        for base in range(2 * d):
            for q in divisors(2 * d - base):
                m = (2 * d - base) // q
                if d <= q * (m // 2) + base:
                    check(2 * (d % q) <= base, "descent degree")
                    if q > base:
                        check(m % 2 == 0 and base == 2 * (d % q), "balanced descent")

    check(D % 8 == 7 and 2 * 7 > 8, "multiple-of-eight cover exclusion")
    for a, expected in EXPECTED.items():
        candidates = [(q, 2 * (D - a) // q) for q in divisors(D - a) if q > linear]
        check(candidates == expected, f"residual list for a={a}")
        print(f"d mod q = {a}: {candidates}")
    check(max(m for row in EXPECTED.values() for _, m in row) == 82, "maximum outer degree")
    # When the common homogeneous degree is zero, a cover of degree >= 3 is
    # homothetic on each fiber, with at most two labels per repeated configuration.
    max_untwisted = 3 * (N - 4 * D + 20) + 16 + 2 * (4 * D // 3) + 20_607_410
    check(max_untwisted < 2 * N, "untwisted proper higher cover")
    print(f"non-toric component degree >= {linear:,}; {sum(map(len, EXPECTED.values()))} large degrees")


if __name__ == "__main__":
    verify()
