#!/usr/bin/env python3
"""Certify single-field locator constancy tests on two fixed order-256 domains."""

import argparse
from itertools import combinations
from math import gcd
import os
from pathlib import Path
import subprocess
import tempfile

from flint import fmpz_mat

from probe_mu64_unit_lattice import require
from probe_mu128_unit_ellipsoid import exponent_rows, kernel_basis
from probe_mu256_joint_transfer import outer_bound, phase, short_basis, verify_fields

ORDER = 256


def expanded_logs(field):
    p, g, z, logs = (field[k] for k in ('prime', 'generator', 'root', 'logs'))
    rows = exponent_rows(ORDER)
    result = [0]
    for j in range(1, ORDER):
        value = (phase(j)*((p-1)//ORDER)+sum(a*row[j] for a, row in zip(logs, rows))) % (p-1)
        require(pow(g, value, p) == (1-pow(z, j, p)) % p, 'dyadic logarithm mismatch')
        result.append(value)
    return result


def observations(logs, order, half_window, sector, modulus):
    """Rows are source coordinates, columns are the congruences at the marked centers."""
    sites = range(half_window+1, order//2)
    if sector == 'lift':
        centers = range(-half_window, half_window+1)
        free = [j for j in range(order//2) if all((j-x) % (order//2) for x in centers)]
        return [[(logs[(j-x) % order]-logs[(j+order//2-x) % order]) % modulus
                 for x in centers] for j in free]

    def difference(x, j):
        return logs[(j-x) % order]-logs[j % order]

    centers = range(1, half_window+1)
    sign = 1 if sector == 'symmetric' else -1
    entries = [[(difference(x, j)+sign*difference(x, -j)) % modulus for x in centers]
               for j in sites]
    if sign == 1:
        entries.append([difference(x, order//2) % modulus for x in centers])
    return entries


def congruence_basis(observed, modulus):
    """Lift through an invertible minor, or intersect the column kernels one by one."""
    n, k = len(observed), len(observed[0])
    for indices in combinations(range(min(n, 15)), k):
        pivot = fmpz_mat([observed[i] for i in indices])
        if gcd(int(pivot.det()), modulus) == 1:
            break
    else:
        basis = fmpz_mat([[int(i == j) for j in range(n)] for i in range(n)])
        for column in zip(*observed):
            values = (basis*fmpz_mat([[a] for a in column])).entries()
            basis = (kernel_basis([int(v) for v in values], modulus)*basis).lll()
        return basis
    inverse, denominator = pivot.inv().numer_denom()
    inverse *= pow(int(denominator), -1, modulus)
    coefficients = (fmpz_mat(observed)*inverse).tolist()
    basis = [[int(i == j) for j in range(n)] for i in range(n)]
    for i in range(n):
        if i in indices:
            basis[i][i] = modulus
        else:
            for j, a in zip(indices, coefficients[i]):
                basis[i][j] = -int(a) % modulus
    basis = fmpz_mat(basis).lll()
    require(abs(int(basis.det())) == modulus**k, 'wrong congruence index')
    require(all(int(x) % modulus == 0 for x in (basis*fmpz_mat(observed)).entries()),
            'basis misses a congruence')
    return basis


def check_sector(field, full_logs, order, width, sector, radius_squared, binary, block):
    modulus = (field['prime']-1)//order
    logs = full_logs[::ORDER//order]
    obs = observations(logs, order, width//2, sector, modulus)
    basis = congruence_basis(obs, modulus)
    n = basis.nrows()
    scale = 2 if sector == 'symmetric' else 1
    weights = [scale]*n
    if sector == 'symmetric':
        weights[-1] = 1
    metric = fmpz_mat([[weights[i]*int(i == j) for j in range(n)] for i in range(n)])
    gram = short_basis(basis*metric*basis.transpose(), block)
    data = ' '.join(map(str, outer_bound(gram, scale, radius_squared)))
    run = subprocess.run([binary], input=data, text=True, check=True, capture_output=True)
    nodes, found = map(int, run.stdout.split())
    require(nodes > 0 and found == 0, f'nonzero candidate in {sector} sector')
    print(f"p={field['prime']}  order={order}  sites={width}  sector={sector}  "
          f"dimension={n}  radius squared={radius_squared}  nodes={nodes}", flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--field', type=int, choices=(1, 2))
    parser.add_argument('--case', choices=('five-pairs', 'nine'))
    parser.add_argument('--block', type=int, default=37, help='BKZ block for the nine-site case')
    args = parser.parse_args()
    path = Path(__file__).resolve().parent
    fields = verify_fields(path/'mu256_unit_logs.json')
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp)/'window-search'
        subprocess.run([os.environ.get('CXX', 'c++'), '-O3', '-std=c++17',
                        str(path/'probe_mu256_joint_transfer.cpp'), '-o', binary], check=True)
        for number, field in enumerate(fields, 1):
            if args.field is not None and args.field != number:
                continue
            logs = expanded_logs(field)
            if args.case in (None, 'five-pairs'):
                for sector in ('symmetric', 'antisymmetric'):
                    check_sector(field, logs, 128, 5, sector, 492, binary, 0)
                check_sector(field, logs, 256, 5, 'lift', 123, binary, 0)
            if args.case in (None, 'nine'):
                for sector in ('symmetric', 'antisymmetric'):
                    check_sector(field, logs, 256, 9, sector, 247, binary, args.block)
