#!/usr/bin/env python3
"""Check all primitive-conductor ternary norms by quadratic descent (python-flint)."""

import argparse
from math import log

from flint import fmpz_poly


def exact_norm(n, exponent):
    """Norm of 1+zeta+zeta^exponent, where zeta has dyadic order n."""
    d = n // 2
    x = fmpz_poly([0, 1])
    f = (1 + x + x**exponent) % (x**d + 1)
    while d > 1:
        coeffs = f.coeffs()
        even = fmpz_poly(coeffs[::2])
        odd = fmpz_poly(coeffs[1::2])
        d //= 2
        f = (even**2 - x * odd**2) % (x**d + 1)
    return abs(int(f[0]))


def unit_support(n, c):
    exponents = (0, 1, c)
    opposite = any((a-b) % n == n//2 for a in exponents for b in exponents)
    progression = any((2*a - sum(exponents) + a) % n == 0 for a in exponents)
    return opposite or progression


def check(n):
    d = n // 2
    threshold, scale = 7**d, 2**d
    minimum = None
    for c in range(n):
        norm = exact_norm(n, c)
        if (norm == 1) != unit_support(n, c):
            raise ArithmeticError(f"unit classification failed at n={n}, c={c}")
        if norm == 1:
            continue
        if scale * norm**8 < threshold:
            raise ArithmeticError(f"norm gap failed at n={n}, c={c}")
        candidate = (norm, c)
        if minimum is None or candidate < minimum:
            minimum = candidate
    norm, exponent = minimum
    print(f"n={n} minimum log(D)/d={log(norm)/d:.6f} at c={exponent}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-exponent", type=int, default=10)
    args = parser.parse_args()
    for j in range(2, args.max_exponent + 1):
        check(2**j)
