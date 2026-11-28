#!/usr/bin/env python3
"""Complete the p1 monomial cross-ratio census on the 128- and 256-site quotients.

uv run --with python-flint python scripts/probes/probe_quarter_monomial_mu128_mu256.py --jobs 4
"""
import argparse
from collections import defaultdict, Counter
from functools import partial
from itertools import combinations
from math import gcd
from multiprocessing import Pool

from probe_quarter_monomial_mu64 import (
    G, N, P, PAIRINGS, check_one_parameter, spectrum_requires_grid_triple,
)


def canonical_spectrum(exponents, grid):
    pairs = [(exponents[i]+exponents[j], exponents[k]+exponents[l])
             for (i, j), (k, l) in PAIRINGS]
    frequencies = set(v % grid for pair in pairs for v in pair)
    choices = []
    for x in frequencies:
        for y in frequencies:
            if (x-y) % 2:
                multiplier = pow((y-x) % grid, -1, grid)
                choices.append(tuple(sorted(tuple(sorted(multiplier*(v-x) % grid for v in pair))
                                            for pair in pairs)))
    return min(choices)


def narrow_subgrid(spectrum, grid, threshold):
    frequencies = set(sum(spectrum, ()))
    required = {v for i, j in spectrum if i != j for v in (i, j)}
    size = grid
    while size >= 8:
        residues = Counter(f % size for f in frequencies)
        if any(residues[f % size] == 1 for f in required):
            for multiplier in range(1, size, 2):
                sites = sorted(multiplier*f % size for f in residues)
                gap = max([v-u for u, v in zip(sites, sites[1:])] + [size+sites[0]-sites[-1]])
                if (size-gap)*(grid//size) < threshold:
                    return True
        size //= 2
    return False


def cyclic_mobius_control():
    """Count nontoric matches to powers on mu32 by their three anchors."""
    grid = 32
    x = [pow(G, h*(N//grid), P) for h in range(grid)]
    worst = 0
    for power in range(grid):
        y = [x[h*power % grid] for h in range(grid)]
        for b, c in combinations(range(1, grid), 2):
            if 1 in (y[b], y[c]) or y[b] == y[c]:
                continue
            if (y[b] == x[b] and y[c] == x[c]) or (y[b]*x[b] % P == 1 and y[c]*x[c] % P == 1):
                continue
            left = (1-x[b])*(1-y[c]) % P
            right = (1-y[b])*(1-x[c]) % P
            matches = sum((left*(x[c]-x[j])*(y[b]-y[j])-right*(y[c]-y[j])*(x[b]-x[j])) % P == 0
                          for j in range(grid))
            worst = max(worst, matches)
    assert worst == 4


def check_tuple(a, roots):
    for free in range(4):
        check_one_parameter(a, free, roots)


def check_grid(grid, jobs):
    threshold = 22 if grid == 128 else 41
    roots = [pow(G, h*(N//grid), P) for h in range(grid)]
    groups = defaultdict(list)
    rejected = {}
    eligible = 0
    for tail in combinations(range(1, grid//2+11), 3):
        if gcd(*tail) != 1:
            continue
        a = (0, *tail)
        if grid == 256 and any((i-j) % 32 == 0 for i, j in combinations(a, 2)):
            continue
        cancellation = sum(gcd(j-i, k-i) for i, j, k in combinations(a, 3))
        if a[3]+a[2]-a[1]-cancellation >= grid//4:
            continue
        eligible += 1
        spectrum = canonical_spectrum(a, grid)
        if grid == 256:
            if spectrum not in rejected:
                rejected[spectrum] = narrow_subgrid(spectrum, grid, threshold)
            if rejected[spectrum]:
                continue
        groups[spectrum].append(a)

    rank_test = partial(spectrum_requires_grid_triple, roots=roots, threshold=threshold)
    with Pool(jobs) as workers:
        flags = workers.map(rank_test, groups, chunksize=1)
        remaining = [a for tuples, flag in zip(groups.values(), flags) if flag for a in tuples]
        workers.map(partial(check_tuple, roots=roots), remaining, chunksize=1)
    result = (eligible, sum(map(len, groups.values())), len(groups), len(remaining))
    expected = (3679, 3679, 968, 27) if grid == 128 else (21842, 8134, 1453, 0)
    assert result == expected, result
    print(f"grid={grid} degree-eligible={eligible} retained={result[1]} "
          f"spectra={len(groups)} grid-triple-tuples={len(remaining)}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--grid", type=int, choices=(128, 256))
    args = parser.parse_args()
    cyclic_mobius_control()
    for grid in ([args.grid] if args.grid else [128, 256]):
        check_grid(grid, args.jobs)
