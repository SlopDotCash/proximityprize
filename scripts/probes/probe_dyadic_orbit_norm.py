#!/usr/bin/env python3
"""Check weighted vanisher-ratio transfer on the named quotient grids."""
import json
from fractions import Fraction
from itertools import combinations
from math import floor, gcd, prod
from pathlib import Path

from probe_mu64_unit_lattice import PRIMES, gram_schmidt, prime_factor, require

HERE = Path(__file__).resolve().parent
# Each quotient-site weight is a sum of this many signs in {-1, 0, 1}.
CAPACITY = {16: 2**26, 32: 512}


def inverse(matrix):
    n = len(matrix)
    work = [[Fraction(x) for x in row] + [Fraction(i == j) for j in range(n)]
            for i, row in enumerate(matrix)]
    for i in range(n):
        pivot = next(j for j in range(i, n) if work[j][i])
        work[i], work[pivot] = work[pivot], work[i]
        scale = work[i][i]
        work[i] = [x / scale for x in work[i]]
        for j in range(n):
            if j != i:
                scale = work[j][i]
                work[j] = [x - scale*y for x, y in zip(work[j], work[i])]
    return [row[n:] for row in work]


def quotient_logs(cert, n):
    """Factor 1-z_n^r using primitive units on the order-64 grid and their phases."""
    p, seed = cert['prime'], cert['generator']
    factors = cert['factors']
    require(len({a for a, _ in factors}) == len(factors) and
            all(b > 0 and prime_factor(a) for a, b in factors), "bad factorization")
    modulus = prod(a**b for a, b in factors)
    require((p-1) % modulus == 0 and modulus % n == 0, "bad projection order")
    require(all(pow(seed, (p-1)//a, p) != 1 for a, _ in factors), "wrong generator")
    z = pow(seed, (p-1)//n, p)
    require(pow(z, n//2, p) == p-1, "wrong quotient root order")
    units, logs = [], []
    for r in range(1, n//2, 2):
        logarithm = 0
        for j in range(r, 64, n):
            logarithm += cert['logs'][min(j, 64-j)//2]
            if j > 32:
                logarithm += (p-1)//2 + j*((p-1)//64)
        u = (1-pow(z, r, p)) % p
        logarithm %= modulus
        require(pow(seed, logarithm*((p-1)//modulus), p) == pow(u, (p-1)//modulus, p),
                "quotient-unit logarithm disagrees")
        units.append(u)
        logs.append(logarithm)
    return units, logs, modulus//n


def products(factors, radii, p):
    """Enumerate signed products without recomputing variable powers in inner loops."""
    tables = []
    for g, extent in zip(factors, radii):
        value = pow(g, -extent, p)
        row = []
        for _ in range(2*extent+1):
            row.append(value)
            value = value*g % p
        tables.append(row)

    def visit(i, value):
        if i == len(tables):
            yield value
        else:
            for u in tables[i]:
                yield from visit(i+1, value*u % p)
    return visit(0, 1)


def certify(cert, n, basis):
    p, d = cert['prime'], n//4
    units, logs, modulus = quotient_logs(cert, n)
    require(len(basis) == d and all(len(row) == d for row in basis), "wrong basis size")
    require(all(sum(a*b for a,b in zip(row, logs)) % modulus == 0 for row in basis),
            "basis misses congruence")
    _, squares = gram_schmidt(basis)
    require(prod(squares) == (modulus//gcd(modulus, *logs))**2, "incorrect basis index")
    bound = 4*(n.bit_length()-1)*CAPACITY[n]
    inverse_basis = inverse(basis)
    radii = [floor(bound*sum(abs(row[j]) for row in inverse_basis)) for j in range(d)]
    generators = [prod(pow(u,n*a,p) for u,a in zip(units, row)) % p for row in basis]
    sizes = [2*t+1 for t in radii]
    total = prod(sizes)
    left = min(combinations(range(d), d//2),
               key=lambda s: max(prod(sizes[j] for j in s),total//prod(sizes[j] for j in s)))
    right = tuple(j for j in range(d) if j not in left)
    if prod(sizes[j] for j in left) > prod(sizes[j] for j in right):
        left, right = right, left
    left_products = set(products([generators[j] for j in left], [radii[j] for j in left], p))
    left_size = prod(sizes[j] for j in left)
    require(len(left_products) == left_size, "left signed products collided")
    hits = sum(x in left_products for x in products([generators[j] for j in right],
                                                   [radii[j] for j in right], p))
    require(hits == 1, "nonzero full-field relation in coefficient rectangle")
    print(f"p{PRIMES.index(p)+1} order {n}: exponent bound {bound}, coordinates {radii}, "
          f"products {left_size}+{total//left_size}, one match", flush=True)


if __name__ == '__main__':
    data = json.loads((HERE/'mu64_unit_lattice_certificates.json').read_text())
    bases = json.loads((HERE/'dyadic_orbit_norm_bases.json').read_text())
    require(tuple(row['prime'] for row in data) == PRIMES and len(bases) == len(data),
            "named-prime coverage")
    for cert, tables in zip(data, bases):
        for order in CAPACITY:
            certify(cert, order, tables[str(order)])
