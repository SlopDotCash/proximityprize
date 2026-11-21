#!/usr/bin/env python3
"""Classify all split primes supporting an antipodal-free sum at order 16."""

from itertools import product
from math import isqrt, lcm


def norm(coeffs):
    """Descend by A(X) A(-X), with Y=X^2 and Y^(d/2)=-1."""
    if len(coeffs) == 1:
        return coeffs[0]
    m = len(coeffs) // 2
    reduced = [0] * m
    for i, a in enumerate(coeffs):
        for j, b in enumerate(coeffs):
            if (i + j) % 2:
                continue
            exponent = (i + j) // 2
            sign = (-1)**(j + exponent//m)
            reduced[exponent % m] += sign * a * b
    return norm(reduced)


def main():
    configs = [v for v in product((0, 1, -1), repeat=8) if any(v)]
    norms = {norm(v) for v in configs}
    common_multiple = lcm(*norms)
    if len(configs) != 6560 or len(norms) != 41 or min(norms) != 1 or max(norms) != 2401:
        raise ArithmeticError("incorrect norm census")
    if common_multiple != 19578399097634641832363784947218309144704:
        raise ArithmeticError("incorrect common multiple")
    primes = [
        p for p in range(17, max(norms)+1, 16)
        if all(p % q for q in range(2, isqrt(p)+1)) and common_multiple % p == 0
    ]
    if primes != [17, 97, 113, 193, 241, 337, 353, 401, 433, 577, 881]:
        raise ArithmeticError("incorrect split prime set")
    print("6560 nonzero signed configurations, 41 norms, maximum 2401")
    for p in primes:
        root = next(h for h in range(2, p) if pow(h, 8, p) == p-1)
        powers = [pow(root, i, p) for i in range(8)]
        witness = next(v for v in configs if sum(a*t for a, t in zip(v, powers)) % p == 0)
        values = {(a*t) % p for a, t in zip(witness, powers) if a}
        if not values or values & {-v % p for v in values} or sum(values) % p:
            raise ArithmeticError("invalid first-moment witness")
        print(f"p={p}, primitive root of order 16={root}, subset={sorted(values)}")


if __name__ == "__main__":
    main()
