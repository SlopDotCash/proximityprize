#!/usr/bin/env python3
"""Verify the named-prime order-64 unit lattice certificates using exact arithmetic."""
import argparse
import json
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path

PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)
ORDER = 64
DIMENSION = 16
BOUND = 24


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def prime_factor(q):
    if q == 2:
        return True
    return q > 2 and q % 2 and all(q % j for j in range(3, isqrt(q)+1, 2))


def gram_schmidt(basis):
    """Exact row Gram–Schmidt coefficients and squared orthogonal lengths."""
    n = len(basis)
    mu = [[Fraction(0)]*n for _ in basis]
    lengths = []
    for i, row in enumerate(basis):
        for j in range(i):
            dot = sum(x*y for x, y in zip(row, basis[j]))
            correction = sum(mu[i][k]*mu[j][k]*lengths[k] for k in range(j))
            mu[i][j] = (dot-correction)/lengths[j]
        norm = sum(x*x for x in row)
        lengths.append(Fraction(norm)-sum(mu[i][k]**2*lengths[k] for k in range(i)))
        require(lengths[-1] > 0, "dependent lattice basis")
    return mu, lengths


def sphere(basis, mu, lengths):
    """Enumerate every lattice vector in the circumscribed Euclidean ball."""
    n = len(basis)
    coordinates = [0]*n

    def visit(i, remaining):
        if i < 0:
            yield tuple(sum(coordinates[j]*basis[j][k] for j in range(n)) for k in range(n))
            return
        center = -sum((coordinates[j]*mu[j][i] for j in range(i+1, n)), Fraction(0))
        squared = remaining * center.denominator**2 / lengths[i]
        radius = isqrt(squared.numerator // squared.denominator)
        lo = -((radius-center.numerator) // center.denominator)
        hi = (radius+center.numerator) // center.denominator
        for value in range(lo, hi+1):
            coordinates[i] = value
            yield from visit(i-1, remaining - (value-center)**2 * lengths[i])

    yield from visit(n-1, Fraction(n*BOUND**2))


def verify(cert, prime, reverse):
    require(cert['prime'] == prime, "wrong named prime")
    seed, logs = cert['generator'], cert['logs']
    factors, basis = cert['factors'], cert['basis']
    require(len(logs) == DIMENSION and len(basis) == DIMENSION and
            all(len(row) == DIMENSION for row in basis), "wrong certificate dimensions")
    require(len(set(q for q,_ in factors)) == len(factors) and
            all(e > 0 and prime_factor(q) for q,e in factors), "bad smooth factorization")
    modulus = prod(q**e for q,e in factors)
    require((prime-1) % modulus == 0 and modulus % ORDER == 0, "bad projected group order")
    require(all(pow(seed, (prime-1)//q, prime) != 1 for q,_ in factors),
            "projected generator has deficient order")
    zeta = pow(seed, (prime-1)//ORDER, prime)
    require(pow(zeta, ORDER//2, prime) == prime-1, "wrong evaluation-domain order")
    units = [(1-pow(zeta, j, prime)) % prime for j in range(1, ORDER//2, 2)]
    projection = (prime-1)//modulus
    require(all(pow(seed, a*projection, prime) == pow(u, projection, prime)
                for a,u in zip(logs, units)), "projected logarithm mismatch")
    reduced = modulus//ORDER
    index = reduced//gcd(reduced, *logs)
    require(all(sum(v*a for v,a in zip(row, logs)) % reduced == 0 for row in basis),
            "basis vector is outside the congruence kernel")
    if reverse:
        basis = list(reversed(basis))
    mu, lengths = gram_schmidt(basis)
    require(prod(lengths) == index**2, "basis has incorrect lattice index")
    total = box = identities = 0
    for v in sphere(basis, mu, lengths):
        total += 1
        if max(map(abs, v)) > BOUND:
            continue
        box += 1
        if prod(pow(u, ORDER*a, prime) for u,a in zip(units, v)) % prime == 1:
            require(not any(v), f"nontrivial bounded relation {v}")
            identities += 1
    require(identities == 1, "zero exponent vector was missed")
    return total, box, identities


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-basis', action='store_true')
    args = parser.parse_args()
    data = json.loads(Path(__file__).with_name('mu64_unit_lattice_certificates.json').read_text())
    require(len(data) == len(PRIMES), "missing named field")
    for cert, prime in zip(data, PRIMES):
        total, box, identities = verify(cert, prime, args.reverse_basis)
        print(f"p={prime}  sphere={total}  box={box}  identities={identities}", flush=True)
