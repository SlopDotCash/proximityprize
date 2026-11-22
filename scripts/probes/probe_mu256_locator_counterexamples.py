#!/usr/bin/env python3
"""Recheck the two literal Lean examples in the finite fields and in Z[X]/(X^128+1)."""

import re
from math import prod
from pathlib import Path

from probe_mu64_unit_lattice import PRIMES, require

LEAN = (Path(__file__).resolve().parents[2] / 'ArkLib/Research/ProximityGap/Frontier'
        / 'Order256LocatorCounterexamples.lean')


def read_example(source, name):
    start = source.index(f'def {name} : Example where\n')
    body = source[start:source.index('\n\n', start)]
    data = {}
    for label in ('prime', 'root', 'value'):
        data[label] = int(re.search(rf'^\s*{label} := (\d+)$', body, re.M).group(1))
    for label in ('numerator', 'denominator', 'centers'):
        match = re.search(rf'\b{label} :=\s*\[([\d,\s]+)\]', body)
        data[label] = [int(v) for v in match.group(1).split(',')]
    return data


def finite_values(p, root, numer, denom):
    powers = [pow(root, i, p) for i in range(256)]
    require(len(set(powers)) == 256 and pow(root, 256, p) == 1, 'incorrect root order')
    values = {}
    for i, a in enumerate(powers):
        if i in numer or i in denom:
            continue
        top = prod((a-powers[j]) % p for j in numer) % p
        bottom = prod((a-powers[j]) % p for j in denom) % p
        values[i] = top * pow(bottom, -1, p) % p
    return values


def cyclotomic_product(i, first, j, second):
    """Multiply the binomials, reducing each power of X with X^128=-1."""
    coefficients = [1]+[0]*127
    for center, sites in ((i, first), (j, second)):
        for site in sites:
            updated = [0]*128
            for degree, coefficient in enumerate(coefficients):
                for sign, power in ((1, degree+center), (-1, degree+site)):
                    reduced = power % 256
                    updated[reduced % 128] += (sign if reduced < 128 else -sign)*coefficient
            coefficients = updated
    return coefficients


def verify(data, p, expected_constant, expected_asymmetric):
    z, value = data['root'], data['value']
    numer, denom, centers = (data[k] for k in ('numerator', 'denominator', 'centers'))
    require(data['prime'] == p and len(numer) == len(denom) == 62 and len(centers) == 4,
            'incorrect field or cardinality')
    all_sites = numer+denom+centers
    require(len(all_sites) == len(set(all_sites)) and all(0 <= j < 256 for j in all_sites),
            'exponents alias or supports overlap')
    require(all(j % 2 == 0 for j in centers), 'centers must have the same parity')
    require(all((-j) % 256 in sites for sites in (numer, denom) for j in sites),
            'missing inverse in support')
    finite = finite_values(p, z, numer, denom)
    require(sorted(j for j, v in finite.items() if v == value) == centers, 'wrong finite fiber')
    auxiliary = finite_values(257, 3, numer, denom)
    i, j = centers[:2]
    require(auxiliary[i] != auxiliary[j], 'auxiliary prime does not separate the pair')
    left = cyclotomic_product(i, numer, j, denom)
    right = cyclotomic_product(i, denom, j, numer)
    constant = left[0]-right[0]
    require(constant == expected_constant and constant != 0, 'wrong cyclotomic remainder')
    changed = sum((j+128) % 256 not in sites for sites in (numer, denom) for j in sites if j % 2)
    require(changed == expected_asymmetric, 'wrong antipodal asymmetry count')
    print(f'p={p}  centers={centers}  degree=62  value={value}  '
          f'constant={constant}  changed odd sites={changed}')


if __name__ == '__main__':
    source = LEAN.read_text()
    verify(read_example(source, 'first'), PRIMES[0], -3601468257152, 58)
    verify(read_example(source, 'second'), PRIMES[1], -18117040, 60)
