#!/usr/bin/env python3
"""Exact ellipsoid tests for order-128 subset-vanisher ratio comparisons.

Requires python-flint for integral linear algebra. Every basis replacement used
for pruning is checked by its inverse or its determinant.
"""
import argparse
import json
from math import factorial, gcd, isqrt, prod
from pathlib import Path

from flint import fmpz_mat

from probe_mu64_unit_lattice import PRIMES, lattice_coordinates, orthogonal_lengths, require

ORDER = 128
FACTOR_TABLE = {
    10455338053: {2:2, 3:2, 223:1, 829:1, 1571:1},
    379484152867: {2:1, 3:2, 7:1, 13:1, 31:1, 7473397:1},
    202172094073993: {2:3, 3:1, 7:1, 462983:1, 2599243:1},
    462478642316479903: {2:1, 3:1, 479:1, 15391:1, 10455338053:1},
    45154452767952660479: {2:1, 59494517:1, 379484152867:1},
    90308905535905320959: {2:1, 45154452767952660479:1},
    PRIMES[0]: {2:36, 7:3, 26407:1, 279991:1, 4533259:1, 462478642316479903:1},
    PRIMES[1]: {2:30, 3:1, 5:2, 7:1, 71:1, 202172094073993:1, 90308905535905320959:1},
}


def certify_prime(n):
    if n not in FACTOR_TABLE:
        require(2 <= n < 10**8 and all(n % i for i in range(2, isqrt(n)+1)),
                "uncertified prime factor")
        return
    factors = FACTOR_TABLE[n]
    require(prod(q**e for q,e in factors.items()) == n-1, "incorrect factorization")
    for q in factors:
        certify_prime(q)
    witness = next(a for a in range(2, 10000) if pow(a, n-1, n) == 1 and
                   all(gcd(pow(a, (n-1)//q, n)-1, n) == 1 for q in factors))
    require(witness < n, "invalid primality witness")


def exponent_rows(order=ORDER):
    return [[sum((sign*(1 << level)*r) % order == d
                 for sign in (1, -1) for level in range(order.bit_length()-1))
             for d in range(order)] for r in range(1, order//2, 2)]


def bezout(a, b):
    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q, r = divmod(a, b)
        a, b = b, r
        x0, x1 = x1, x0-q*x1
        y0, y1 = y1, y0-q*y1
    return a, x0, y0


def kernel_basis(logs, modulus):
    """Complete integral kernel of a single row modulo the group order."""
    dim = len(logs)
    basis = [[int(i == j) for j in range(dim)] for i in range(dim)]
    row = [v % modulus for v in logs]
    for j in range(1, dim):
        if not row[j]:
            continue
        a, b = row[0], row[j]
        divisor, x, y = bezout(a, b)
        old, other = basis[0], basis[j]
        basis[0] = [x*s+y*t for s,t in zip(old, other)]
        basis[j] = [(-b//divisor)*s+(a//divisor)*t for s,t in zip(old, other)]
        row[0], row[j] = divisor, 0
    index = modulus//gcd(modulus, row[0])
    basis[0] = [index*x for x in basis[0]]
    result = fmpz_mat(basis).lll()
    require(abs(int(result.det())) == index, "incorrect kernel index")
    require(all(sum(int(v)*a for v,a in zip(r, logs)) % modulus == 0
                for r in result.tolist()), "incorrect kernel generator")
    return result


def check_shift(rows, h, logs, order, bound):
    matrix = fmpz_mat([[r[j]-r[(j-h) % ORDER] for j in range(ORDER) if j not in (0,h)]
                       for r in rows])
    if h == ORDER//2:
        require(all(sum(col) == 0 for col in matrix.transpose().tolist()),
                "antipodal coordinate elimination failed")
        matrix = fmpz_mat(matrix.tolist()[:-1])
        logs = [a-logs[-1] for a in logs[:-1]]
    dim = matrix.nrows()
    identity = fmpz_mat([[int(i == j) for j in range(dim)] for i in range(dim)])
    covariance = matrix*matrix.transpose()
    metric, scale = covariance.inv().numer_denom()
    require(covariance*metric == scale*identity and scale > 0, "bad projection metric")

    # Any integral superlattice of the image would suffice. Check containment directly.
    image = fmpz_mat(matrix.transpose().hnf().tolist()[:dim])
    _, denominator = (matrix.transpose()*image.inv()).numer_denom()
    require(denominator == 1, "image lattice misses an exponent column")
    transformed_logs = [sum(int(v)*a for v,a in zip(row, logs)) for row in image.tolist()]
    basis = kernel_basis(transformed_logs, order)*image
    initial = basis*metric*basis.transpose()
    reduced, transform = initial.lll(transform=True, rep='gram', gram='exact')
    require(abs(int(transform.det())) == 1 and transform*initial*transform.transpose() == reduced,
            "basis reduction changed the lattice or quadratic form")
    points = 0
    mu, lengths = orthogonal_lengths([[int(v) for v in row] for row in reduced.tolist()])
    for vector in lattice_coordinates(mu, lengths, int(scale)*bound):
        points += 1
        if any(vector):
            e = (fmpz_mat([vector])*transform*basis).tolist()[0]
            raise ArithmeticError(f"nonzero candidate at shift {h}: {e}")
    require(points == 1, "zero vector missing")
    return points


def order256_limit():
    """Minkowski volume lower bound at the two named primes for displacement two."""
    n = 256
    rows = exponent_rows(n)
    matrix = fmpz_mat([[r[j]-r[(j-2) % n] for j in range(n) if j not in (0,2)] for r in rows])
    source = matrix.transpose()
    generators, transform = source.hnf(transform=True)
    require(transform*source == generators, "bad integer image generators")
    subindex = abs(int(fmpz_mat(generators.tolist()[:64]).det()))
    determinant = int((matrix*source).det())
    require(subindex == 2 and determinant == 614560623940147206055138107999571273706286146912256,
            "incorrect order-256 displacement matrix")
    maximum_index = subindex*((max(PRIMES)-1)//n)
    require((3*74)**64*determinant > (factorial(32)*2**64*maximum_index)**2,
            "Minkowski estimate is insufficient")


def run_field(cert, shifts, bound):
    p, g, z, logs = cert['prime'], cert['generator'], cert['root'], cert['logs']
    require(p in PRIMES, "wrong prime")
    certify_prime(p)
    require(all(pow(g, (p-1)//q, p) != 1 for q in FACTOR_TABLE[p]),
            "generator has deficient order")
    require(pow(z, ORDER//2, p) == p-1 and len(logs) == ORDER//4, "bad root or log list")
    require(all(pow(g,a,p) == (1-pow(z,r,p)) % p for a,r in zip(logs,range(1,ORDER//2,2))),
            "full-field unit logarithm mismatch")
    rows = exponent_rows()
    return [check_shift(rows, h, logs, (p-1)//ORDER, bound) for h in shifts]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--field', type=int, choices=(1,2))
    parser.add_argument('--data', type=Path, default=Path(__file__).with_name('mu128_unit_logs.json'))
    parser.add_argument('--shifts', type=int, nargs='+', choices=range(1,65))
    parser.add_argument('--bound', type=int, default=126)
    args = parser.parse_args()
    order256_limit()
    certs = json.loads(args.data.read_text())
    shifts = args.shifts or range(1,65)
    expected = PRIMES if args.field is None else (PRIMES[args.field-1],)
    for p in expected:
        cert = next(c for c in certs if c['prime'] == p)
        counts = run_field(cert, shifts, args.bound)
        print(f"p={p}  displacements={len(counts)}  total vectors={sum(counts)}", flush=True)
