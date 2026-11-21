#!/usr/bin/env python3
"""Reconstruct all balanced four-head cubic splines on μ16 and count actual labels."""

import argparse
from collections import Counter
from itertools import permutations

from probe_quarter_opposite_pairs import census, indices

EDGES = ((0, 1), (0, 2), (1, 2), (2, 3), (1, 3), (0, 3))
P1 = 365375409332725729550921208179070755120141565953
P2 = 730750818665451459101842416358141509841924915201
GENERIC = {16: 29184, 21: 2048, 22: 1024}
EXPECTED = {
    97: {16: 38400, 19: 256, 20: 768, 21: 1536, 22: 512, 32: 1536},
    65537: GENERIC, P1: GENERIC, P2: GENERIC,
}


def nullspace(rows, p):
    """Right kernel over the prime field, with one vector per free column."""
    dimension = len(rows[0])
    pivots = []
    for j in range(dimension):
        rank = len(pivots)
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = pow(rows[rank][j], -1, p)
        rows[rank] = [a * scale % p for a in rows[rank]]
        for i, row in enumerate(rows):
            if i != rank and row[j]:
                factor = row[j]
                rows[i] = [(a - factor*b) % p for a, b in zip(row, rows[rank])]
        pivots.append(j)
    basis = []
    for free in sorted(set(range(dimension)) - set(pivots)):
        vector = [0] * dimension
        vector[free] = 1
        for i, j in enumerate(pivots):
            vector[j] = -rows[i][free] % p
        basis.append(vector)
    return basis


def polynomial_value(coefficients, x, p):
    result = 0
    for c in reversed(coefficients):
        result = (result*x + c) % p
    return result


def direction(owner, foreign, p):
    da, db = ((b-a) % p for a, b in zip(owner, foreign))
    assert da or db
    return -da * pow(db, -1, p) % p if db else p


def row_splines(xs, edge_at, p):
    rows = []
    for i, edge in edge_at.items():
        row = [0] * 12
        for h, sign in zip(edge, (1, -1)):
            if h:
                for j in range(4):
                    row[(h-1)*4+j] = sign * pow(xs[i], j, p) % p
        rows.append(row)
    basis = nullspace(rows, p)
    # A different kernel dimension requires a new analysis of admissible row planes.
    assert len(basis) == 2
    cubics = [[(0, 0, 0, 0)] + [row[j:j+4] for j in (0, 4, 8)] for row in basis]
    return [[tuple(polynomial_value(row[h], x, p) for row in cubics) for h in range(4)]
            for x in xs]


def verify_labels(heads, owner_at, p, expected):
    """Choose finite coordinates and directly check the witness at each label."""
    def value(i, h):
        a, b = heads[i][h]
        return a, (b + shear*a) % p

    for shear in range(37):
        if all(v == row[h] or (v[1]-row[h][1] + shear*(v[0]-row[h][0])) % p
               for row, h in zip(heads, owner_at) for v in row):
            break
    else:
        raise AssertionError("36 opportunities exclude at most 36 shear values")
    received = [value(i, h) for i, h in enumerate(owner_at)]
    labels = set()
    for h in range(4):
        polynomial = [value(i, h) for i in range(16)]
        core = [i for i in range(16) if received[i] == polynomial[i]]
        assert len(core) == 7
        for i in set(range(16)) - set(core):
            label = direction(received[i], polynomial[i], p)
            assert label != p
            labels.add(label)
            sites = core + [i]
            assert all((received[j][0] + label*received[j][1]
                        - polynomial[j][0] - label*polynomial[j][1]) % p == 0 for j in sites)
            # A joint cubic on these eight sites agrees at seven core sites with
            # this polynomial pair, hence equals it and fails at i.
            assert received[i] != polynomial[i]
    assert len(labels) == expected


def run(p):
    generator = next(g for g in range(2, p) if pow(g, (p-1)//2, p) == p-1)
    zeta = pow(generator, (p-1)//16, p)
    xs = [pow(zeta, i, p) for i in range(16)]
    assert len(set(xs)) == 16 and pow(zeta, 16, p) == 1
    histogram = Counter()
    best = 0

    def visit(holes, unions, head, _coeffs, weight):
        nonlocal best
        strata = tuple(head) + tuple(a ^ b for a, b in zip(unions, head))
        edge_at = {i: edge for mask, edge in zip(strata, EDGES) for i in indices(mask)}
        hole_sites = tuple(indices(holes))
        assert set(edge_at) == set(range(16)) - set(hole_sites)
        heads = row_splines(xs, edge_at, p)
        baseline = set()
        for i, edge in edge_at.items():
            owner = heads[i][edge[0]]
            assert tuple(h for h in range(4) if heads[i][h] == owner) == edge
            baseline.update(direction(owner, v, p) for v in heads[i] if v != owner)
        options = {}
        for i in hole_sites:
            assert len(set(heads[i])) == 4
            for h, owner in enumerate(heads[i]):
                options[i, h] = {direction(owner, v, p) for v in heads[i] if v != owner}
        for owners in permutations(range(4)):
            slots = dict(zip(hole_sites, owners))
            count = len(baseline.union(*(options[key] for key in slots.items())))
            histogram[count] += weight
            if count > best:
                owner_at = [edge_at[i][0] if i in edge_at else slots[i] for i in range(16)]
                verify_labels(heads, owner_at, p, count)
                best = count

    totals = census(p, generator, visit)
    assert sum(histogram.values()) == 24 * totals['relations']
    assert dict(histogram) == EXPECTED[p]
    print(f"{p} weighted assignments by actual label count {dict(sorted(histogram.items()))}")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('primes', type=int, nargs='*', help='default: all four tested fields')
    for prime in parser.parse_args().primes or EXPECTED:
        run(prime)
