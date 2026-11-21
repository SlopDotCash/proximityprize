#!/usr/bin/env python3
"""Test rational multipliers of the production 2^30 subgroups by exact modular powering."""

from argparse import ArgumentParser
from math import gcd, prod

ORDER = 1 << 30
# Factorizations certified in _PrizeShapePrimeP30 and _PrizeShapePrimeP30Second.
PRIMES = {
    365375409332725729550921208179070755120141565953:
        {2: 36, 7: 3, 26407: 1, 279991: 1, 4533259: 1, 462478642316479903: 1},
    730750818665451459101842416358141509841924915201:
        {2: 30, 3: 1, 5: 2, 7: 1, 71: 1, 202172094073993: 1, 90308905535905320959: 1},
}


def doubling_orbit(prime, factorization):
    if prod(q ** e for q, e in factorization.items()) != prime - 1:
        raise ValueError("factorization does not match the group order")
    order = prime - 1
    for q in factorization:
        while order % q == 0 and pow(2, order // q, prime) == 1:
            order //= q
    return order // gcd(order, ORDER)


def first_collision(prime, height):
    if not 1 <= height < prime:
        raise ValueError("height must lie between 1 and p-1")
    powers = {}
    for numerator in range(1, height + 1):
        value = pow(numerator, ORDER, prime)
        if value in powers:
            return powers[value], numerator
        powers[value] = numerator
    return None


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, default=1 << 20)
    args = parser.parse_args()
    for prime, factors in PRIMES.items():
        orbit = doubling_orbit(prime, factors)
        print(f"p={prime} doubling orbit={orbit} cycles={(prime - 1) // (ORDER * orbit)}")
        pair = first_collision(prime, args.height)
        if pair is None:
            print(f"p={prime} height={args.height} all powers distinct", flush=True)
        else:
            print(f"p={prime} height={args.height} collision={pair}", flush=True)


if __name__ == "__main__":
    main()
