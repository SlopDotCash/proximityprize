#!/usr/bin/env python3
"""Test scalar projections of saturated septics against lifted cubic pair layouts."""

import argparse
from collections import Counter
from itertools import combinations, permutations, product

from probe_quarter_sixteen_splines import EDGES, P1, P2, census, indices, row_splines

EDGES_SORTED = tuple(combinations(range(4), 2))
LIFT_PRIME = 553 * 2**768 + 1


def canonical_layout(edge_at):
    """Quotient by rotations, inversion, and simultaneous head relabelling."""
    sites = tuple(edge_at.get(i) for i in range(16))
    canonical = None
    for permutation in permutations(range(4)):
        relabel = {edge: EDGES_SORTED.index(tuple(sorted(permutation[h] for h in edge))) + 1
                   for edge in EDGES_SORTED}
        encoded = tuple(relabel[e] if e else 0 for e in sites)
        for order in (encoded, encoded[::-1]):
            for i, label in enumerate(order):
                if label == 0:
                    candidate = order[i:] + order[:i]
                    if canonical is None or candidate < canonical:
                        canonical = candidate
    return canonical


def templates():
    layouts = set()

    def visit(_holes, blocks, positive, _coeffs, _weight):
        strata = positive + tuple(block ^ side for block, side in zip(blocks, positive))
        edge_at = {i: edge for edge, side in zip(EDGES, strata) for i in indices(side)}
        layouts.add(canonical_layout(edge_at))

    generator = next(a for a in range(2, 256) if pow(a, (P1-1)//2, P1) == P1-1)
    census(P1, generator, visit)
    assert len(layouts) == 28
    cubic = ((0, 2, 4), (5, 13), (14,), (6,), (7, 15), (8, 10, 12))
    layouts.add(canonical_layout({i: edge for edge, sites in zip(EDGES_SORTED, cubic) for i in sites}))
    assert len(layouts) == 29
    return sorted(layouts)


def slope_sets(layout, p):
    generator = next(a for a in range(2, 256) if pow(a, (p-1)//2, p) == p-1)
    z = pow(generator, (p-1)//32, p)
    assert pow(z, 16, p) == p-1
    xs = [pow(z, i, p) for i in range(32)]
    edge_at = {i: EDGES_SORTED[e-1] for i, e in enumerate(layout) if e}
    planes = row_splines([x*x % p for x in xs[:16]], edge_at, p)
    differences = [[((b[0]-a[0]) % p, (b[1]-a[1]) % p)
                    for a, b in combinations(row, 2) if a != b] for row in planes]
    # Choose a scalar basis with finite slopes for every nonzero difference.
    t = next(t for t in range(97) if all((dy+t*dx) % p for row in differences for dx, dy in row))
    slopes = [{-dx * pow((dy+t*dx) % p, -1, p) % p for dx, dy in row} for row in differences]
    return xs, set(range(16))-set(edge_at), slopes*2


def interpolate(x1, x2, x3, y1, y2, y3, p):
    """Recover the projective matrix taking three distinct finite sources to the targets."""
    left = (y3-y2)*(x3-x1) % p
    right = (y3-y1)*(x3-x2) % p
    coeff = ((left*y1-right*y2) % p, (right*y2*x1-left*y1*x2) % p,
             (left-right) % p, (right*x1-left*x2) % p)
    scale = pow(next(c for c in coeff if c), -1, p)
    return tuple(c*scale % p for c in coeff)


def power_contacts(a, b, p):
    """Maximum number of solutions of M(x^a)=x^b on the 32nd roots."""
    generator = next(g for g in range(2, 256) if pow(g, (p-1)//2, p) == p-1)
    z = pow(generator, (p-1)//32, p)
    graph = [(pow(z, i*a, p), pow(z, i*b, p)) for i in range(32)]
    assert len(set(graph)) == 32
    maps = set()
    for group in combinations(graph, 3):
        sources, targets = zip(*group)
        if len(set(sources)) == len(set(targets)) == 3:
            maps.add(interpolate(*sources, *targets, p))
    return max(sum((u*x+v-y*(w*x+t)) % p == 0 for x,y in graph) for u,v,w,t in maps)


def count_contacts(layout, p):
    xs, half_holes, slopes = slope_sets(layout, p)
    holes = sorted(half_holes | {i+16 for i in half_holes})
    candidates = set()
    for i, j, k in combinations(holes, 3):
        x1, x2, x3 = (xs[t] for t in (i, j, k))
        for y1, y2, y3 in product(slopes[i], slopes[j], slopes[k]):
            if len({y1, y2, y3}) < 3:
                continue
            candidates.add(interpolate(x1, x2, x3, y1, y2, y3, p))

    counts = Counter()
    for a, b, c, d in candidates:
        def hits(i):
            den = (c*xs[i]+d) % p
            if not den:
                return False
            num = (a*xs[i]+b) % p
            return any((den*y-num) % p == 0 for y in slopes[i])

        private = sum(hits(i) for i in holes)
        if private >= 4:
            alternate = private + sum(hits(i) for i in range(32) if i % 16 not in half_holes)
            counts[private, alternate] += 1
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    primes = {'control': 65537, 'first': P1, 'second': P2, 'lift': LIFT_PRIME}
    parser.add_argument('--fields', nargs='+', choices=primes, default=list(primes))
    args = parser.parse_args()
    # Proth certificate. The prime exceeds the norm bound for every augmented matrix.
    assert 553 < 2**768 and pow(3, (LIFT_PRIME-1)//2, LIFT_PRIME) == LIFT_PRIME-1
    layouts = templates()
    for name in args.fields:
        total = Counter()
        for layout in layouts:
            total.update(count_contacts(layout, primes[name]))
        power_max = tuple(power_contacts(a, b, primes[name]) for a, b in [(1, 5), (1, 4), (2, 3)])
        assert power_max == (4, 3, 3)
        print(name, len(layouts), dict(total), power_max, flush=True)
        assert total == {(4, 4): 72}
