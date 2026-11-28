#!/usr/bin/env python3
"""Run the six-site mod-3 search and specialize its survivors at both primes."""
import argparse
from collections import Counter
from itertools import combinations, product
from math import prod
from pathlib import Path
import subprocess
import tempfile

from probe_linear_contact_quotient import require
from probe_mu32_four_cubics import PAIRS


FIELDS = ((365375409332725729550921208179070755120141565953, 3),
          (730750818665451459101842416358141509841924915201, 37))


def sites(even_mask, odd_mask):
    return tuple([2*i for i in range(64) if even_mask >> i & 1] +
                 [2*i+shift for i in range(32) if odd_mask >> i & 1 for shift in (1, 65)])


def check_kernels(reverse_pivots):
    source = Path(__file__).with_suffix('.cpp')
    with tempfile.TemporaryDirectory() as directory:
        binary = Path(directory) / 'search'
        subprocess.run(['c++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror', source,
                        '-o', binary], check=True)
        options = ['--reverse-pivots'] if reverse_pivots else []
        result = subprocess.run([binary, *options], capture_output=True, text=True, check=True)
    require(result.stderr.strip() == 'Six even orbits 38494, four even plus odd pair 9952, '
            'directed candidates 6', 'orbit and directed survivor counts')
    directed = set()
    for line in result.stdout.splitlines():
        paired, centers, a, b, c, d = map(int, line.split())
        t, u, v = sites(centers, paired), sites(a, b), sites(c, d)
        require((len(t), len(u), len(v)) == (6, 7, 7) and len(set(t+u+v)) == 20,
                'disjoint supports of the correct sizes')
        directed.add((t, u, v))
    require(len(directed) == 6 and all((t, v, u) in directed for t, u, v in directed),
            'candidate pair orientation')
    return sorted((t, u, v) for t, u, v in directed if u < v)


def check_field(prime, generator, candidates):
    z = pow(generator, (prime-1)//128, prime)
    require(pow(z, 64, prime) == prime-1, 'primitive grid root')
    points = [pow(z, j, prime) for j in range(128)]

    def locator(a, x):
        return prod(x-points[j] for j in a) % prime

    maxima = []
    for tests, a, b in candidates:
        ratios = {i: locator(a, x)*pow(locator(b, x), -1, prime) % prime
                  for i, x in enumerate(points) if i not in a and i not in b}
        require(len({ratios[i] for i in tests}) > 1, 'surviving anchors are not constant')
        maxima.append(max(Counter(ratios.values()).values()))
    require(sorted(maxima) == [1, 4, 4], 'maximum nonzero finite fibers on the entire grid')
    print(f'p={prime} maximum fiber sizes {sorted(maxima)}')


def check_cubic_witness(prime, generator):
    z = pow(generator, (prime-1)//128, prime)
    grid = [pow(z, j, prime) for j in range(128)]
    roots = [[grid[4*j] for j in PAIRS[0, i]] for i in (1, 2, 3)]

    def cubic(root_set, x):
        return prod(x-y for y in root_set) % prime

    a, b, c = roots
    at_b, at_c = grid[4*6], grid[4*14]
    scales = [1, cubic(a, at_b)*pow(cubic(b, at_b), -1, prime) % prime,
              cubic(a, at_c)*pow(cubic(c, at_c), -1, prime) % prime]
    words = [[0]*128] + [[scale*cubic(root_set, x*x % prime) % prime for x in grid]
                         for scale, root_set in zip(scales, roots)]
    require(len(set(map(tuple, words))) == 4, 'distinct padded cubics')
    center = [None]*128
    for (i, j), indices in PAIRS.items():
        for t in indices:
            for k in (2*t, 2*t+64):
                require(grid[k]**2 % prime == grid[4*t], 'physical preimage')
                require(words[i][k] == words[j][k] and center[k] is None, 'pair witness')
                center[k] = words[i][k]
    free = iter(k for k in range(128) if center[k] is None)
    for word, private in zip(words, (22, 26, 24, 24)):
        for _ in range(private):
            k = next(free)
            center[k] = word[k]
    hits = [sum(x == y for x, y in zip(word, center)) for word in words]
    require(all(x is not None for x in center) and min(hits) >= 40, 'four-word center')
    print(f'p={prime} padded cubic agreement counts {hits}')


def check_quartet():
    edges = list(combinations(range(4), 2))
    triples = list(combinations(range(4), 3))
    for loss in product(range(3), repeat=6):
        deficit = sum(loss)
        if deficit > 2:
            continue
        # Each common triple costs at least one unit. No all-four site can fit.
        good = 0
        for triple in triples:
            gaps = sorted(loss[edges.index(e)] for e in combinations(triple, 2))
            good += gaps[:2] == [0, 0] and gaps[2] <= 1
        require(good > 2-deficit, 'a suitable triangle survives all triple collisions')
    n = 2**30
    k = n//16
    s = n//128
    hits = n-715827882
    require(128+39 < 4*42 and 3*42 <= 128, 'exact three at small-grid radius 86')
    require(n+3*(k-1)+s*(39-3*7) < 4*hits, 'production degree-seven quotient excluded')
    require(n+3*(k-1)+s*(3*6) < 4*hits, 'all lower quotient degrees excluded')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reverse-pivots', action='store_true')
    args = parser.parse_args()
    candidates = check_kernels(args.reverse_pivots)
    for prime, generator in FIELDS:
        check_field(prime, generator, candidates)
        check_cubic_witness(prime, generator)
    check_quartet()
    print('48,446 test orbits, three unordered signed pairs, zero sextuple fibers.')
