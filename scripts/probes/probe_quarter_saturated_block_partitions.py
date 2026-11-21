#!/usr/bin/env python3
"""Test the minor relation for six consecutive balanced strata on the second prime."""
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, prod

P = 730750818665451459101842416358141509841924915201
G = 192152681249815148642741928588691886362054863855
N = 2**30
D = N // 4 - 1
S = 2 * D // 3
EDGES = tuple(combinations(range(4), 2))


def normalized_labelings():
    """Take a representative for every ordering up to relabelling the four heads."""
    seen = set()
    for order in permutations(EDGES):
        if order in seen:
            continue
        yield order
        for perm in permutations(range(4)):
            seen.add(tuple(tuple(sorted((perm[i], perm[j]))) for i, j in order))


@lru_cache(None)
def interval_moments(start, size=S, generator=G):
    """Power sums of roots and inverse roots, and their product, for one long block."""
    def total(k):
        ratio = pow(generator, k, P)
        return pow(ratio, start, P) * (pow(ratio, size, P)-1) * pow(ratio-1, -1, P) % P
    return tuple(total(k) for k in (1, 2, 3, -1, -2, -3)), pow(generator, size*(2*start+size-1)//2, P)


def minor_column(starts, size=S, generator=G):
    """Eight endpoint coefficients of the monic degree-2D triangle locator."""
    blocks = [interval_moments(a, size, generator) for a in starts]
    powers = [sum(row[0][j] for row in blocks) % P for j in range(6)]
    constant = prod(row[1] for row in blocks) % P
    def terms(s1, s2, s3):
        return (-s1 % P, (s1*s1-s2)*pow(2, -1, P) % P,
                -(s1**3-3*s1*s2+2*s3)*pow(6, -1, P) % P)
    top = terms(*powers[:3])
    bottom = terms(*powers[3:])
    return (1, *top, constant, *(constant*a % P for a in bottom))


def independent(columns):
    basis = {}
    for column in columns:
        v = list(column)
        for i in range(len(v)):
            if not v[i]:
                continue
            if i not in basis:
                inv = pow(v[i], -1, P)
                basis[i] = [x*inv % P for x in v]
                break
            scale = v[i]
            v = [(x-scale*y) % P for x, y in zip(v, basis[i])]
        else:
            return False
    return True


def check_direct():
    """Compare all reported coefficients against a direct product on 32 roots."""
    g = pow(G, N//32, P)
    for starts in combinations((0, 5, 10, 15, 20, 25), 3):
        coefficients = [1]
        for start in starts:
            for exponent in range(start, start+4):
                root = pow(g, exponent, P)
                multiplied = [0]*(len(coefficients)+1)
                for j, value in enumerate(coefficients):
                    multiplied[j] -= root*value
                    multiplied[j+1] += value
                coefficients = [a % P for a in multiplied]
        assert minor_column(starts, 4, g) == tuple(coefficients[:-5:-1]+coefficients[:4])


def main():
    check_direct()
    assert 6*S+4 == N and 3*S == 2*D
    assert pow(G, N, P) == 1 and pow(G, N//2, P) != 1
    labelings = tuple(normalized_labelings())
    assert len(labelings) == 30
    tested = 0
    failures = []
    for gaps in product(range(5), repeat=6):
        if sum(gaps) != 4:
            continue
        starts = [0]
        for gap in gaps[:-1]:
            starts.append(starts[-1]+S+gap)
        assert starts[-1]+S+gaps[-1] == N
        locators = {idx: minor_column([starts[j] for j in idx])
                    for idx in combinations(range(6), 3)}
        for order in labelings:
            cols = [locators[tuple(j for j, edge in enumerate(order) if i not in edge)]
                    for i in range(4)]
            tested += 1
            if not independent(cols):
                failures.append((gaps, order))
    print(f'{tested} systems up to head renaming, {24*tested} labelled allocations')
    print(f'{len(failures)} systems survive the eight-coefficient rank test')
    if failures:
        print(failures[:3])
    assert tested == 30*comb(9, 5)
    assert not failures


if __name__ == '__main__':
    main()
