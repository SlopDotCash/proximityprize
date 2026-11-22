#!/usr/bin/env python3
"""Exhaust the six ternary face-ratio conditions at length 32.

Requires NumPy. The first stage uses exact modular row reduction on integer
cyclotomic-unit exponents. Later stages specialize ratio identities at 65537.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product

import numpy as np

N = 32
FIELD = 65537
ROOT = pow(3, (FIELD-1)//N, FIELD)
POINTS = tuple(pow(ROOT, j, FIELD) for j in range(N))


def mask(sites):
    return sum(1 << x for x in sites)


def representatives(size):
    """Translation puts one site at exponent zero; odd multipliers give Galois conjugates."""
    seen = set()
    for rest in combinations(range(1, N), size-1):
        sites = (0,) + rest
        if mask(sites) in seen:
            continue
        for base in sites:
            for unit in range(1, N, 2):
                seen.add(mask((unit*(x-base) % N) for x in sites))
        yield sites


def unit_exponents():
    """Odd representatives modulo sign after factoring 1-zeta^d."""
    exponents = np.zeros((N, N//4), dtype=np.int64)
    for d in range(1, N):
        multiplicity = d & -d
        for j in range(multiplicity):
            r = (d//multiplicity + j*(N//multiplicity)) % N
            exponents[d, (min(r, N-r)-1)//2] += 1
    return exponents


EXPONENTS = unit_exponents()


def kernel(center, prime):
    sites = np.array([x for x in range(N) if x not in center])
    factors = EXPONENTS[(sites[None, :] - np.array(center)[:, None]) % N]
    differences = factors[1:] - factors[0]
    matrix = differences.transpose(0, 2, 1).reshape(-1, len(sites)).copy() % prime
    pivots, free = [], []
    for col in range(len(sites)):
        row = len(pivots)
        choices = np.flatnonzero(matrix[row:, col])
        if len(choices) == 0:
            free.append(col)
            continue
        pivot = row + choices[0]
        matrix[[row, pivot]] = matrix[[pivot, row]]
        matrix[row] = matrix[row] * pow(int(matrix[row, col]), -1, prime) % prime
        coefficients = matrix[:, col].copy()
        coefficients[row] = 0
        matrix = (matrix - coefficients[:, None]*matrix[row]) % prime
        pivots.append(col)
    return sites, matrix[:len(pivots), free], pivots, free


@lru_cache(None)
def ternary_columns(dimension):
    return np.array(list(product((-1, 0, 1), repeat=dimension)), dtype=np.int64).T


@lru_cache(maxsize=200000)
def locator(sites, t):
    result = 1
    for x in sites:
        result = result * (POINTS[t] - POINTS[x]) % FIELD
    return result


def constant_ratio(plus, minus, center):
    ratios = {locator(plus,t)*pow(locator(minus,t), -1, FIELD) % FIELD for t in center}
    return len(ratios) <= 1


def coarse_pairs(center, prime, statistics):
    sites, matrix, pivots, free = kernel(center, prime)
    statistics['max_nullity'] = max(statistics['max_nullity'], len(free))
    choices = ternary_columns(len(free))
    determined = (-matrix @ choices) % prime
    for col in np.flatnonzero(np.isin(determined, [0, 1, prime-1]).all(axis=0)):
        w = np.zeros(len(sites), dtype=np.int64)
        w[pivots], w[free] = determined[:, col], choices[:, col]
        plus = tuple(map(int, sites[w == 1]))
        minus = tuple(map(int, sites[(w == -1) | (w == prime-1)]))
        required = 14-len(center)
        if len(plus) != required or len(minus) != required or plus >= minus:
            continue
        if constant_ratio(plus, minus, center):
            yield plus, minus


def split_table(sites, size, test, power):
    return [(part, [pow(locator(part,t), power, FIELD) for t in test])
            for part in combinations(sites, size)]


def orientations(a, plus, minus):
    size = len(a)
    test = sorted(set(range(N)) - set(a + plus + minus))
    weight = [locator(minus,t)*pow(locator(plus,t), -1, FIELD) % FIELD for t in test]
    for b_size in range(size+1):
        if not 0 <= len(plus)-b_size <= size:
            continue
        right = split_table(minus, b_size, test, -2)
        for b, values in split_table(plus, b_size, test, 2):
            row = [x*y % FIELD for x,y in zip(weight, values)]
            cp = tuple(sorted(set(plus) - set(b)))
            for bp, inverse in right:
                ratios = [x*y % FIELD for x,y in zip(row, inverse)]
                for value, count in Counter(ratios).items():
                    if count < size:
                        continue
                    c = tuple(sorted(set(minus) - set(bp)))
                    fiber = [t for t,x in zip(test, ratios) if x == value]
                    for ap in combinations(fiber, size):
                        yield a, ap, b, bp, c, cp


def all_ratios(edges):
    for i, center in enumerate(edges):
        j = 2*((i//2+1) % 3)
        k = 2*((i//2+2) % 3)
        plus = tuple(sorted(edges[j] + edges[k+1-i%2]))
        minus = tuple(sorted(edges[j+1] + edges[k+i%2]))
        if not constant_ratio(plus, minus, center):
            return False
    return True


def main(prime):
    if pow(ROOT, 16, FIELD) != FIELD-1:
        raise ArithmeticError("wrong order for the specialization root")
    survivors = []
    for size in (5, 6, 7):
        stats = Counter()
        for a in representatives(size):
            stats['representatives'] += 1
            for plus, minus in coarse_pairs(a, prime, stats):
                stats['coarse'] += 1
                for edges in orientations(a, plus, minus):
                    stats['oriented'] += 1
                    if not all_ratios(edges):
                        continue
                    masks = tuple(mask(e) for e in edges)
                    print('surviving labeled stratum masks', *masks)
                    if any(any((x+16) % N not in e for x in e) for e in edges):
                        raise ArithmeticError(f"noninvariant layout: {edges}")
                    stats['survivors'] += 1
                    survivors.append(masks)
        print(size, dict(stats))
    if len(survivors) != 2:
        raise ArithmeticError("unexpected final layout count")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank-prime', type=int, choices=(101, 103), default=101)
    main(parser.parse_args().rank_prime)
