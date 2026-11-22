#!/usr/bin/env python3
"""Certify bounded independent cyclotomic-unit exponent vectors at the two named primes."""
from itertools import product

PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)
BOUND = 20


def half_products(units, p):
    """Enumerate every signed exponent vector on four chosen units."""
    powers = [[pow(u, e, p) for e in range(-BOUND, BOUND + 1)] for u in units]
    first = [x*y % p for x, y in product(*powers[:2])]
    last = [x*y % p for x, y in product(*powers[2:])]
    for x in first:
        for y in last:
            yield x*y % p


def check(p):
    seed = next(a for a in range(2, 256) if pow(a, (p-1)//2, p) == p-1)
    zeta = pow(seed, (p-1)//32, p)
    if pow(zeta, 16, p) != p-1:
        raise ArithmeticError("root has incorrect order")
    units = [pow(1 - pow(zeta, r, p), 32, p) for r in range(1, 16, 2)]
    left = set(half_products(units[:4], p))
    expected = (2*BOUND + 1)**4
    if len(left) != expected or 1 not in left:
        raise ArithmeticError("first-half products were not distinct")
    matches = 0
    for value in half_products(units[4:], p):
        if value in left:
            if value != 1:
                raise ArithmeticError("bounded unit relation found")
            matches += 1
    if matches != 1:
        raise ArithmeticError("expected only the two zero vectors to match")
    return expected


if __name__ == "__main__":
    for prime in PRIMES:
        count = check(prime)
        print(f"p={prime}: {count} products per half, only the zero vectors match", flush=True)
