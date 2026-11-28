#!/usr/bin/env python3
"""Verify all five-site fibers for pairs of full quintics, sextics and septics."""
import argparse
from collections import Counter
from itertools import combinations, permutations, product
from math import prod
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from probe_linear_contact_quotient import require
from probe_mu128_septic_kernel import FIELDS, sites


HISTOGRAMS = {5: {1: 2, 4: 6}, 6: {1: 8, 2: 318, 3: 4, 4: 275, 6: 996},
              7: {1: 35, 2: 31, 3: 9, 4: 18}}


def rows(binary, degree, direct, reverse):
    args = [binary, '--five-tests']
    if degree != 7:
        args.append({5: '--five-roots', 6: '--six-roots'}[degree])
    if reverse:
        args.append('--reverse-pivots')
    if direct:
        args.append('--direct-search')
    result = subprocess.run(args, check=True, capture_output=True, text=True)
    size = 2*sum(HISTOGRAMS[degree].values())
    require(result.stderr.strip() == 'Five even orbits 4085, three even plus odd pair 651, '
            f'directed candidates {size}', 'orbit and weight enumeration')
    result_set = set()
    for line in result.stdout.splitlines():
        odd, t, a, b, c, d = map(int, line.split())
        t, a, b = (tuple(sorted(z)) for z in (sites(t, odd), sites(a, b), sites(c, d)))
        require((len(t), len(a), len(b)) == (5, degree, degree)
                and len(set(t+a+b)) == 5+2*degree, 'candidate support sizes')
        result_set.add((t, a, b))
    require(len(result_set) == size and all((t, b, a) in result_set for t, a, b in result_set),
            'orientation closure')
    return sorted((t, a, b) for t, a, b in result_set if a < b)


def verify_field(prime, generator, degree, candidates):
    z = pow(generator, (prime-1)//128, prime)
    require(pow(z, 64, prime) == prime-1, 'primitive root')
    points = [pow(z, j, prime) for j in range(128)]
    histogram = Counter()
    equal = 0
    for tests, a, b in candidates:
        ratios = {}
        for j, x in enumerate(points):
            if j in a or j in b:
                continue
            top = prod(x-points[i] for i in a)
            bottom = prod(x-points[i] for i in b)
            ratios[j] = top*pow(bottom, -1, prime) % prime
        histogram[max(Counter(ratios.values()).values())] += 1
        if len({ratios[i] for i in tests}) > 1:
            continue
        equal += 1
        full = {i for i, v in ratios.items() if v == ratios[tests[0]]}
        require(degree == 6 and len(full) == 6, 'fifth site forces a full sextic fiber')
        for support in (a, b, full):
            require(set(support) == {(i+64) % 128 for i in support}, 'antipodal completion')
    require(histogram == HISTOGRAMS[degree] and equal == (280 if degree == 6 else 0),
            'fiber histograms and equal test tuples')
    print(f'p={prime} degree {degree} equal five-site tuples {equal}, histogram '
          f'{dict(sorted(histogram.items()))}')


def sextic_patterns():
    edges = list(combinations(range(4), 2))
    triangles = list(combinations(range(4), 3))
    survivors = set()
    # A quadruple site would consume all three allowed lost coincidences.
    # Removing its linear factor then gives a forbidden full quintic triangle.
    for losses in product(range(4), repeat=6):
        deficit = sum(losses)
        if deficit > 3:
            continue
        ranks = [6-d for d in losses]
        for common in product(range(4-deficit), repeat=4):
            waste = sum(common)
            if deficit+waste > 3:
                continue
            even_edges = set()
            possible = True
            for triangle, shared in zip(triangles, common):
                ids = [edges.index(e) for e in combinations(triangle, 2)]
                counts = sorted(ranks[i] for i in ids)
                if (shared == 0 and counts == [5, 6, 6]) or (shared == 1 and counts == [6]*3):
                    possible = False
                    break
                if shared == 0 and counts == [6]*3:
                    even_edges.update(ids)
            # Two different full unpolluted triangles give four words in a
            # common translate of the cubics in X², with coincidence count ≤32.
            if not possible or len(even_edges) > 3:
                continue

            def relabel(perm):
                bad_edges = {tuple(sorted(perm[i] for i in e)): d for e, d in zip(edges, losses)}
                bad_triangles = {tuple(sorted(perm[i] for i in t)): c for t, c in zip(triangles, common)}
                return tuple(bad_edges[e] for e in edges), tuple(bad_triangles[t] for t in triangles)
            survivors.add(min(relabel(p) for p in permutations(range(4))))
    require(survivors == {((0, 0, 1, 0, 1, 1), (0, 0, 0, 0))},
            'only a full triangle and three five-root edges survive')
    print('Sextic C≥33 leaves only pair counts 6,6,6 around a triangle and 5,5,5 to its fourth word.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-pivots', action='store_true')
    parser.add_argument('--direct-search', action='store_true',
                        help='independent ordinary ternary depth-first traversal (slower)')
    args = parser.parse_args()
    source = Path(__file__).with_name('probe_mu128_septic_kernel.cpp')
    with TemporaryDirectory() as directory:
        binary = Path(directory) / 'search'
        subprocess.run(['c++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror',
                        source, '-o', binary], check=True)
        for degree in (5, 6, 7):
            candidates = rows(binary, degree, args.direct_search, args.reverse_pivots)
            for p, g in FIELDS:
                verify_field(p, g, degree, candidates)
    sextic_patterns()
