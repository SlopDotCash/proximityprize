#!/usr/bin/env python3
"""Check simultaneous order-256 vanisher comparisons in the two named prime fields.

Requires python-flint and a C++17 compiler. Optional fpylll accelerates reduction.
The verifier checks the integral transforms even when an approximate BKZ routine
produces them. The branch search uses an outer bound rounded in integer arithmetic.
"""

import argparse
import json
import os
import subprocess
import tempfile
from math import isqrt
from pathlib import Path

from flint import fmpq, fmpz_mat

from probe_mu128_unit_ellipsoid import FACTOR_TABLE, certify_prime, exponent_rows, kernel_basis
from probe_mu64_unit_lattice import PRIMES, require

ORDER = 256
RADIUS_SQUARED = 254


def verify_fields(path):
    fields = json.loads(path.read_text())
    require([d['prime'] for d in fields] == list(PRIMES), 'expected the two named primes')
    for field in fields:
        p, g, z = (field[k] for k in ('prime', 'generator', 'root'))
        certify_prime(p)
        require(0 < g < p and all(pow(g, (p-1)//q, p) != 1 for q in FACTOR_TABLE[p]),
                'seed is not primitive')
        require(z == pow(g, (p-1)//ORDER, p) and pow(z, ORDER//2, p) == p-1, 'wrong root')
        logs = field['logs']
        require(len(logs) == ORDER//4 and all(pow(g, a, p) == (1-pow(z, j, p)) % p
                for a, j in zip(logs, range(1, ORDER//2, 2))), 'unit logarithm mismatch')
    return fields


def phase(s):
    valuation_factor = s & -s
    odd = s // valuation_factor
    lifts = (odd + i*(ORDER//valuation_factor) for i in range(valuation_factor))
    return sum(ORDER//2 + j for j in lifts if j > ORDER//2) % ORDER


def ratio_lattice(h, rows, fields):
    sites = [j for j in range(ORDER) if j not in (0, h)]
    matrix = fmpz_mat([[row[j]-row[(j-h) % ORDER] for j in sites] for row in rows])
    logs = [f['logs'] for f in fields]
    if h == ORDER//2:
        require(all(sum(c) == 0 for c in matrix.transpose().tolist()), 'antipodal chart failed')
        matrix = fmpz_mat(matrix.tolist()[:-1])
        logs = [[a-row[-1] for a in row[:-1]] for row in logs]
    dim = matrix.nrows()
    columns = [list(map(int, c))+[(phase(j)-phase((j-h) % ORDER)-h) % ORDER]
               for c, j in zip(matrix.transpose().tolist(), sites)]
    source = fmpz_mat(columns+[[0]*dim+[ORDER]])
    basis = fmpz_mat(source.hnf().tolist()[:dim+1])
    require((source*basis.inv()).numer_denom()[1] == 1, 'image misses a source column')
    for field, coordinates in zip(fields, logs):
        p, z, g = (field[k] for k in ('prime', 'root', 'generator'))
        characters = coordinates + [(p-1)//ORDER]
        for j, col in zip(sites, columns):
            v = (1-pow(z, j, p))*pow((pow(z, h, p)-pow(z, j, p)) % p, -1, p) % p
            require(pow(g, sum(a*b for a, b in zip(col, characters)), p) == v, 'wrong site factor')
        row = [sum(a*b for a, b in zip(line, characters)) for line in basis.tolist()]
        basis = kernel_basis(row, p-1)*basis
    projection = fmpz_mat([row[:-1] for row in basis.tolist()])
    image = fmpz_mat(projection.hnf().tolist()[:dim])
    require((projection*image.inv()).numer_denom()[1] == 1, 'projection lost a lattice point')
    return matrix, image


def short_basis(gram, block):
    reduced, transform = gram.lll(transform=True, rep='gram', gram='exact')
    if block:
        from fpylll import BKZ, FPLLL, GSO, LLL, IntegerMatrix
        FPLLL.set_precision(512)
        n = reduced.nrows()
        raw = IntegerMatrix.from_matrix([[int(v) for v in row] for row in reduced.tolist()])
        change = IntegerMatrix.identity(n)
        metric = GSO.Mat(raw, U=change, flags=GSO.INT_GRAM, float_type='mpfr',
                         gram=True, update=True)
        BKZ.Reduction(metric, LLL.Reduction(metric), BKZ.Param(block_size=block, max_loops=3))()
        update = fmpz_mat([[change[i, j] for j in range(n)] for i in range(n)])
        transform = update*transform
        reduced = update*reduced*update.transpose()
    require(abs(int(transform.det())) == 1 and transform*gram*transform.transpose() == reduced,
            'reduction changed the quadratic form or lattice')
    return reduced


def outer_bound(gram, scale, radius_squared=RADIUS_SQUARED):
    """Return rigorous integer lower bounds on all Gram–Schmidt summands."""
    n = gram.nrows()
    entries = gram.tolist()
    mu = [[fmpq(0) for _ in range(n)] for _ in range(n)]
    diagonal = []
    for i in range(n):
        for j in range(i):
            correction = sum(mu[i][k]*mu[j][k]*diagonal[k] for k in range(j))
            mu[i][j] = (entries[i][j]-correction)/diagonal[j]
        diagonal.append(fmpq(entries[i][i])-sum(mu[i][k]**2*diagonal[k] for k in range(i)))
    denom, unit = 1024, 8192
    weights = [int(length*denom/scale) for length in diagonal]
    require(all(0 < w <= length*denom/scale < w+1 for w, length in zip(weights, diagonal)),
            'invalid diagonal enclosure')
    coefficients = [[int(x*unit) for x in row] for row in mu]
    require(all(abs(x*unit-m) < 1 for row, integers in zip(mu, coefficients)
                for x, m in zip(row, integers)), 'invalid off-diagonal enclosure')
    inverse = gram.inv()
    caps = [isqrt(int(radius_squared*scale*inverse[i, i])) for i in range(n)]
    return [n, radius_squared*denom*unit**2, unit, *weights, *caps,
            *(m for row in coefficients for m in row)]


def verify_shift(h, rows, fields, binary, block):
    matrix, lattice = ratio_lattice(h, rows, fields)
    covariance = matrix*matrix.transpose()
    metric, scale = covariance.inv().numer_denom()
    dim = matrix.nrows()
    identity = fmpz_mat([[int(i == j) for j in range(dim)] for i in range(dim)])
    require(scale > 0 and covariance*metric == scale*identity,
            'incorrect projection metric')
    gram = short_basis(lattice*metric*lattice.transpose(), block)
    data = ' '.join(map(str, outer_bound(gram, scale)))
    result = subprocess.run([binary], input=data, text=True, capture_output=True, check=True)
    nodes, hit = map(int, result.stdout.split())
    require(nodes > 0 and hit == 0, f'nonzero rounded candidate at shift {h}')
    return nodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--block', type=int, default=36, help='BKZ block, 0 uses exact LLL only')
    parser.add_argument('--shifts', nargs='+', type=int, choices=range(1, 129))
    args = parser.parse_args()
    base = Path(__file__).resolve()
    fields = verify_fields(base.with_name('mu256_unit_logs.json'))
    rows = exponent_rows(ORDER)
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp)/'joint-search'
        subprocess.run([os.environ.get('CXX', 'c++'), '-O3', '-std=c++17', str(base.with_suffix('.cpp')),
                        '-o', binary], check=True)
        for h in args.shifts or range(1, 129):
            print(f'shift {h}: {verify_shift(h, rows, fields, binary, args.block)} nodes, zero nonzero candidates',
                  flush=True)


if __name__ == '__main__':
    main()
