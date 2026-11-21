#!/usr/bin/env python3
"""Enclose the dyadic-harmonic determinant upper bound using rational intervals.

For d = 256 and n = 2^30 the first nine terms of the positive majorization
of squared phase distances suffice at both prize primes. No periods are
evaluated numerically. Half-angle and positive-root intervals use integers.
"""

from fractions import Fraction
from math import isqrt


PRECISION = 10**32
LENGTH = 2**30
DIMENSION = 256


def even_harmonic_sum(depth):
    """Bounds for sum_{1 <= j <= depth} 2(1-cos(pi/2^j))^2."""
    scale = PRECISION
    cos_lo = cos_hi = -scale
    lower = upper = Fraction(0)
    for _ in range(depth):
        cos_lo = isqrt(scale * (scale + cos_lo) // 2)
        cos_hi = isqrt(scale * (scale + cos_hi) // 2) + 1
        if not 0 <= cos_lo <= cos_hi <= scale:
            raise ArithmeticError("half-angle enclosure outside [0,1]")
        lower += 2 * Fraction(scale - cos_hi, scale) ** 2
        upper += 2 * Fraction(scale - cos_lo, scale) ** 2
    return lower, upper


def inverse_root(p):
    """Rational bounds for p^(-1/128), certified by powering at the endpoints."""
    exponent = DIMENSION // 2
    target = PRECISION**exponent
    lo, hi = 0, PRECISION
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if p * mid**exponent <= target:
            lo = mid
        else:
            hi = mid
    if not p * lo**exponent <= target < p * hi**exponent:
        raise ArithmeticError("inverse root enclosure failed")
    return Fraction(lo, PRECISION), Fraction(hi, PRECISION)


def main():
    even_lo, even_hi = even_harmonic_sum(8)
    for p, floor in (
        (LENGTH * (2**128 + 192) + 1, 18_077_811),
        (LENGTH * (2**129 + 13) + 1, 17_980_181),
    ):
        base_lo, base_hi = inverse_root(p)
        half_lo, half_hi = inverse_root(2*p)
        gap_lo = (LENGTH // DIMENSION) * (8 * half_lo + even_lo * base_lo)
        gap_hi = (LENGTH // DIMENSION) * (8 * half_hi + even_hi * base_hi)
        if not floor < gap_lo <= gap_hi < floor + 1:
            raise ArithmeticError("nine-term improvement outside certified interval")
        print(f"p={p}, nine-term gap in ({floor}, {floor+1}), |eta| < {LENGTH-floor}")


if __name__ == "__main__":
    main()
