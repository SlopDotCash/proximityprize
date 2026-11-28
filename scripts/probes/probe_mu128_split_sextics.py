#!/usr/bin/env python3
"""Classify split sextic pencils at order 128, then test the reduced cubic quartets."""
import argparse
from collections import defaultdict
from functools import cache
from itertools import combinations
from math import prod
from pathlib import Path
import subprocess
import tempfile

from probe_linear_contact_quotient import require
from probe_mu128_septic_kernel import FIELDS, sites


def candidates(reverse):
    source = Path(__file__).with_name('probe_mu128_septic_kernel.cpp')
    with tempfile.TemporaryDirectory() as directory:
        binary = Path(directory) / 'census'
        subprocess.run(['c++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror',
                        source, '-o', binary], check=True)
        options = ['--six-roots'] + (['--reverse-pivots'] if reverse else [])
        result = subprocess.run([binary, *options], check=True, text=True, capture_output=True)
    require(result.stderr.strip() == 'Six even orbits 38494, four even plus odd pair 9952, '
            'directed candidates 1828', 'sextic census counts')
    rows = set()
    for line in result.stdout.splitlines():
        pair, t, a, b, c, d = map(int, line.split())
        rows.add((tuple(sorted(sites(t, pair))), tuple(sorted(sites(a, b))),
                  tuple(sorted(sites(c, d)))))
    require(len(rows) == 1828 and all((t, b, a) in rows for t, a, b in rows),
            'orientation and duplicates')
    return [(t, a, b) for t, a, b in rows if a < b]


def full_triples(prime, generator, rows):
    z = pow(generator, (prime-1)//128, prime)
    require(pow(z, 64, prime) == prime-1, 'primitive root')
    points = [pow(z, j, prime) for j in range(128)]

    @cache
    def locator(roots, j):
        return prod(points[j]-points[a] for a in roots) % prime

    triples = set()
    for t, a, b in rows:
        require(len(t) == len(a) == len(b) == 6 and len(set(a+b+t)) == 18,
                'disjoint full supports')
        if all((locator(a, j)*locator(b, t[0])-locator(b, j)*locator(a, t[0])) % prime == 0
               for j in t):
            triples.add(tuple(sorted((a, b, t))))
    require(len(triples) == 142, 'specialized candidate triples')
    for triple in triples:
        for support in triple:
            require({(i+64) % 128 for i in support} == set(support),
                    'full fibers must be antipodal')
    return {tuple(sorted(tuple(sorted({i % 64 for i in support})) for support in triple))
            for triple in triples}


def image(support, u, v):
    return tuple(sorted((u*i+v) % 64 for i in support))


def anchored_pairs(triples):
    anchored = defaultdict(set)
    for triple in triples:
        for j in range(3):
            a, b, c = triple[j], triple[(j+1) % 3], triple[(j+2) % 3]
            key, u, v = min((image(a, u, -u*t), u, -u*t) for u in range(1, 64, 2) for t in a)
            b, c = image(b, u, v), image(c, u, v)
            for m in range(1, 64, 2):
                for t in key:
                    v = -m*t
                    if image(key, m, v) == key:
                        h, k = image(b, m, v), image(c, m, v)
                        anchored[key].update(((h, k), (k, h)))
    return anchored


def inspect_cubics(prime, generator, anchored):
    root = pow(generator, (prime-1)//64, prime)
    best = 0
    for u in range(1, 64, 2):
        # Re-evaluate every possible primitive-root relabeling in the named
        # field. A relation linking *three* independent cubic scales receives
        # no assumption of Galois invariance in this step.
        points = [pow(root, u*j, prime) for j in range(64)]

        @cache
        def values(support):
            return tuple(prod(x-points[a] for a in support) % prime for x in points)

        for key, pairs in anchored.items():
            first = values(key)
            pool = []
            for b, c in sorted(pairs):
                base = values(b)
                scale = first[c[0]]*pow(base[c[0]], -1, prime) % prime
                second = tuple(z*scale % prime for z in base)
                require(all(first[i] == second[i] for i in c), 'full cubic fiber')
                pool.append(second)
            for f, g in combinations(pool, 2):
                if f == g or sum(y == z for y, z in zip(f, g)) < 1:
                    continue
                score = 0
                for a, b, c in zip(first, f, g):
                    labels = (0, a, b, c)
                    score += max(labels.count(x) for x in labels)-1
                best = max(best, score)
    require(best == 16, 'largest useful coincidence count in the two-full-triangle class')
    print(f'p={prime} split sextic triples 142, reduced cubic maximum {best}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-pivots', action='store_true')
    args = parser.parse_args()
    rows = candidates(args.reverse_pivots)
    for prime, generator in FIELDS:
        triples = full_triples(prime, generator, rows)
        inspect_cubics(prime, generator, anchored_pairs(triples))
