#!/usr/bin/env python3
"""Certify the first-prime 64-site four-head-to-three-head decision and six-center controls."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import prod

N = 1 << 30
S = N // 64
D = N // 4 - 2
T = N - 480946858
EDGES = list(combinations(range(4), 2))
TRIANGLES = [[j for j, edge in enumerate(EDGES) if i not in edge] for i in range(4)]

# Affine site charges are listed as (slope, intercept).
LINES = [(0, i) for i in (1, 2, 3, 4)] + [(i, 1) for i in (1, 2, 3)] + [(4, 0)]
PRICES = sorted({Fraction(0), Fraction(5)} |
                {price for (j, b), (k, c) in combinations(LINES, 2) if j != k
                 and 0 <= (price := Fraction(c-b, j-k)) <= 5})


def local_price_data():
    prices = []
    for price in PRICES:
        den, num = price.denominator, price.numerator
        ordinary = [max(holes*den, den+num*block)
                    for holes, block in zip((4, 3, 2, 2), (1, 2, 2, 3))]
        locator = max(den, 4*num)
        gains = sorted(((locator-v, j) for j, v in enumerate(ordinary) if locator > v),
                       reverse=True)
        prices.append((ordinary, gains, den*(N+1)+4*num*(T-1)))
    return prices


def possible_shape(m, counts, prices):
    for ordinary, gains, needed in prices:
        maximum = S * sum(cost*count for cost, count in zip(ordinary, counts))
        left = D-m*S
        for gain, j in gains:
            use = min(left, S*counts[j])
            maximum += gain*use
            left -= use
        if maximum < needed:
            return False
    return True


def triangle_status(m, common, misses):
    degree = m-common
    if degree <= 0:
        # Any triangle with a full edge then has constant reduced differences.
        # Such a triangle descends under X -> -X.
        assert degree == 0 and min(misses) == 0
        return 'descends'
    assert min(misses) == 0  # At most two omissions across the whole quartet.
    if 3*degree - 2*sum(misses) > 36:
        return 'three-head improvement'
    if misses.count(0) >= 2 and degree-sum(misses) >= 7:
        return 'odd degree' if degree % 2 else 'descends'
    return 'unresolved triangle'


def check_shapes():
    assert 3*N - 6*(T-1) + 3*D + 36*S == N-4
    prices = local_price_data()
    shapes = []
    for m in range(16):
        for a in range(65):
            for b in range(65-a):
                for c in range(65-a-b):
                    d = 64-a-b-c
                    count = (a, b, c, d)
                    defects = 6*m-b-2*c-3*d
                    if defects >= 0 and possible_shape(m, count, prices):
                        shapes.append((m, count, defects))
    assert Counter((m, defects) for m, _, defects in shapes) == {
        (14, 0): 1, (15, 0): 6, (15, 1): 3, (15, 2): 1}
    stats = Counter()
    for m, (_, _, _, triples), defects in shapes:
        for edge_misses in product(range(defects+1), repeat=6):
            if sum(edge_misses) != defects:
                continue
            for first_three in product(range(triples+1), repeat=3):
                last = triples-sum(first_three)
                if last < 0:
                    continue
                populations = (*first_three, last)
                if any(populations[i] > m-max(edge_misses[j] for j in edges)
                       for i, edges in enumerate(TRIANGLES)):
                    stats['too many common roots'] += 1
                    continue
                status = [triangle_status(m, populations[i], [edge_misses[j] for j in edges])
                          for i, edges in enumerate(TRIANGLES)]
                if 'three-head improvement' in status:
                    stats['three-head improvement'] += 1
                elif 'odd degree' in status:
                    stats['odd degree'] += 1
                else:
                    assert status.count('descends') >= 2, (m, edge_misses, populations, status)
                    stats['two descending triangles'] += 1
    print('shapes', len(shapes), 'distributions', dict(stats))


def check_sharp_six():
    first = [10, 13, 18, 29, 42, 44, 45, 50, 60, 61]
    second = [11, 12, 22, 27, 28, 30, 43, 54, 59, 62]
    for p, generator in [((1 << 158)+(192 << 30)+1, 3), ((1 << 159)+(13 << 30)+1, 37)]:
        grid = [pow(generator, j*((p-1)//64), p) for j in range(64)]
        assert len(set(grid)) == 64
        assert 44 in first and (44+32) % 64 not in first
        values = {}
        for k, x in enumerate(grid):
            if k not in first and k not in second:
                up = prod(x-grid[j] for j in first)
                down = prod(x-grid[j] for j in second)
                values[k] = up*pow(down, -1, p) % p
        assert [k for k, value in values.items() if value == values[0]] == [0, 4, 8, 16, 36, 56]
    print('six-center witness on both named grids')


if __name__ == '__main__':
    check_shapes()
    check_sharp_six()
