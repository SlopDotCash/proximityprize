#!/usr/bin/env python3
"""Certify all four-site parallelograms and three-site progressions of antipodal pairs on the two named order-256 domains."""
import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from itertools import combinations, product
import os
from pathlib import Path
import subprocess
import tempfile

from flint import fmpz_mat

from probe_mu64_unit_lattice import require
from probe_mu256_joint_transfer import outer_bound, short_basis, verify_fields
from probe_mu256_locator_windows import congruence_basis, expanded_logs

ORDER = 256


@lru_cache(maxsize=1)
def tables():
    path = Path(__file__).resolve().with_name('mu256_unit_logs.json')
    return [(expanded_logs(field), (field['prime']-1)//ORDER) for field in verify_fields(path)]


def observations(logs, modulus, case, a, b, sign):
    def value(center, j):
        return logs[(j-center) % ORDER]-logs[(j+128-center) % ORDER]

    if case == 'rectangle':
        # {0,a,b,a+b} with a odd and b even. The reflection exchanges parities.
        h = (a+b) % ORDER
        free = [j for j in range(128) if j < (h-j) % 128 and j not in (0,a,b,h % 128)]
        centers = (0,a)
    elif case == 'centered':
        # {±a,±b}. One fixed source remains in each sector.
        h = 0
        free = [j for j in range(1,64) if j not in (a,b)]
        centers = (a,b)
    else:
        # {-a,0,a}. The symmetric sector has no surviving fixed source.
        h = 0
        free = [j for j in range(1,64) if j != a]
        centers = (0,a)
    obs = [[(value(x,j)+sign*value(x,h-j)) % modulus for x in centers] for j in free]
    if case == 'centered':
        fixed = 0 if sign == 1 else 64
        obs.append([value(x,fixed) % modulus for x in centers])
    require(len(obs) == 62, 'incorrect reflection orbit count')
    return obs


def check(entry):
    binary, field, case, a, b, sign = entry
    logs, modulus = tables()[field-1]
    obs = observations(logs, modulus, case, a, b, sign)
    basis = congruence_basis(obs, modulus)
    n = len(obs)
    scale = 2 if case == 'centered' else 1
    weights = [scale]*n
    if case == 'centered':
        weights[-1] = 1
    metric = fmpz_mat([[int(i == j)*weights[i] for j in range(n)] for i in range(n)])
    gram = short_basis(basis*metric*basis.transpose(), 0)
    radius = 992 if case == 'midpoint' else 496
    data = ' '.join(map(str, outer_bound(gram, scale, radius)))
    run = subprocess.run([binary], input=data, text=True, capture_output=True, check=True)
    nodes, hit = map(int, run.stdout.split())
    require(nodes > 0 and hit == 0, f'nonzero candidate at {(field,case,a,b,sign)}')
    return nodes


def check_combinatorial_example():
    sites = (0,2,22,48,52,58,66,67,79,90,95)
    distances = defaultdict(list)
    for a,b in combinations(sites,2):
        distances[min(b-a,128+a-b)].append((a,b))
    repeated = {d:pairs for d,pairs in distances.items() if len(pairs) > 1}
    require(len(distances) == 54 and repeated == {38:[(0,90),(52,90)]},
            'the eleven-site geometric example has changed')


def shapes(case):
    if case == 'rectangle':
        return product(range(1,64,2),range(2,65,2),(-1,1))
    if case == 'centered':
        return ((a,b,sign) for a,b in combinations(range(1,64),2) for sign in (-1,1))
    return product(range(1,64),(0,),(1,))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--field', type=int, choices=(1,2))
    parser.add_argument('--case', choices=('rectangle','centered','midpoint'))
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    require(args.jobs >= 1, 'number of workers must be positive')
    check_combinatorial_example()
    src = Path(__file__).resolve().with_name('probe_mu256_joint_transfer.cpp')
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp)/'paired-search'
        subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++17',str(src),
                        '-o',binary],check=True)
        with ProcessPoolExecutor(args.jobs) as pool:
            for field in ([args.field] if args.field else [1,2]):
                for case in ([args.case] if args.case else ['rectangle','centered','midpoint']):
                    runs = [(str(binary),field,case,a,b,s) for a,b,s in shapes(case)]
                    counts = list(pool.map(check,runs,chunksize=2))
                    print(f'field={field}  case={case}  lattices={len(counts)}  '
                          f'nodes={sum(counts)}  nonzero candidates=0',flush=True)
