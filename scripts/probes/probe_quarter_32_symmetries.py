#!/usr/bin/env python3
"""Screen saturated degree-seven four-head splines with an order-four domain symmetry."""

import argparse
from functools import lru_cache
from itertools import combinations

PRIMES = (65537, 365375409332725729550921208179070755120141565953,
          730750818665451459101842416358141509841924915201)
EDGES = tuple(combinations(range(4), 2))


def row_reduction(p):
    @lru_cache(65536)
    def inverse(a):
        return pow(a, -1, p)

    def extend(basis, row):
        for pivot, v in basis:
            if row[pivot]:
                t = row[pivot]
                row = [(a-t*b) % p for a, b in zip(row, v)]
        for j, a in enumerate(row):
            if a:
                u = inverse(a)
                return basis + [(j, [b*u % p for b in row])]
        return basis

    return extend


def cyclic(p, zeta, extend):
    """Decompose the 24-column quotient into the four rotation characters."""
    r = pow(zeta, 8, p)
    adj = tuple((a, (a+1) % 4) for a in range(4))
    diag = ((0, 2), (1, 3))
    rows = {}
    for i in range(1, 8):
        for a, b in adj + diag:
            rows[i, a, b] = [
                [pow(zeta, i*d, p) * (pow(r, a*(q-d) % 4, p) - pow(r, b*(q-d) % 4, p)) % p
                 for d in range(8) if (d-q) % 4]
                for q in range(4)]

    def visit(i, bases, first_adjacent, adj_left, diag_left):
        if i == 8:
            return 1
        options = []
        if adj_left:
            options.extend(adj[:1] if first_adjacent else adj)
        if diag_left:
            options.extend(diag)
        survivors = 0
        for a, b in options:
            updated = [extend(basis, row) for basis, row in zip(bases, rows[i, a, b])]
            if 24 - sum(map(len, updated)) >= 2:
                adjacent = (a, b) in adj
                survivors += visit(i+1, updated, first_adjacent and not adjacent,
                                   adj_left-int(adjacent), diag_left-int(not adjacent))
        return survivors

    return sum(visit(1, [[], [], [], []], True, 7-d, d) for d in range(4))


def klein(p, zeta, extend, tor, ref, b):
    """Use one half-turn eigenspace for the Klein four acting as tor and ref."""
    def orbit(i):
        return (i, (i+16) % 32, (b-i) % 32, (b+16-i) % 32)

    reps = sorted({min(orbit(i)) for i in range(32)})
    group = (tuple(range(4)), tor, ref, tuple(tor[ref[h]] for h in range(4)))
    assert all(tor[ref[h]] == ref[tor[h]] for h in range(4))
    # On even monomials remove the common row by zeroing the first vertex orbit.
    # On odd monomials only swapped pairs carry a nonzero coefficient.
    cols = []
    for d in range(8):
        orbits = [(h, tor[h]) for h in range(4) if h < tor[h] or h == tor[h] and d % 2 == 0]
        cols.extend((u, v, d) for u, v in (orbits if d % 2 else orbits[1:]))
    assert len(cols) == 12

    def evaluation(i, h):
        return [pow(zeta, (i*d) % 32, p) * (1 if h == u else (-1)**d if h == v else 0)
                for u, v, d in cols]

    def row(i, a, c):
        return [(v-w) % p for v, w in zip(evaluation(i, a), evaluation(i, c))]

    options = {}
    for i in reps:
        options[i] = []
        for a, c in EDGES:
            sites = list(zip(orbit(i), [tuple(sorted((s[a], s[c]))) for s in group]))
            values = dict(sites)
            if len(set(sites)) != len(values):
                continue
            rows = [row(i, a, c)]
            if len(values) == 4:
                rows.append(row((b-i) % 32, ref[a], ref[c]))
            options[i].append(([EDGES.index(e) for e in values.values()], rows))

    def visit(ordinary, basis, counts):
        if not ordinary:
            return int(all(counts[k] == counts[5-k] for k in range(3)))
        site, *rest = ordinary
        survivors = 0
        for inc, rows in options[site]:
            new = counts.copy()
            for e in inc:
                new[e] += 1
            if max(new) > 7:
                continue
            updated = basis
            for v in rows:
                updated = extend(updated, v)
            if len(updated) < 12:
                survivors += visit(rest, updated, new)
        return survivors

    total = 0
    for mask in range(1, 1 << len(reps)):
        holes = [i for j, i in enumerate(reps) if mask >> j & 1]
        if sum(len(set(orbit(i))) for i in holes) == 4:
            ordinary = sorted((i for i in reps if i not in holes), key=lambda i: len(options[i]))
            total += visit(ordinary, [], [0]*6)
    return total


def run(p):
    g = next(a for a in range(2, p) if pow(a, (p-1)//2, p) == p-1)
    z = pow(g, (p-1)//32, p)
    assert pow(z, 16, p) == p-1
    extend = row_reduction(p)
    assert cyclic(p, z, extend) == 0
    transposition = (1, 0, 2, 3)
    double = (2, 3, 0, 1)
    actions = ((double, (1, 0, 3, 2)), (double, (2, 1, 0, 3)),
               (transposition, (0, 1, 3, 2)), (transposition, (1, 0, 3, 2)))
    for tor, ref in actions:
        for b in (0, 1):
            survivors = klein(p, z, extend, tor, ref, b)
            print(f'{p} half-turn {tor} reflection {ref} shift {b} survivors {survivors}', flush=True)
            assert survivors == 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('primes', nargs='*', type=int, help='default: 65537 and both named primes')
    for prime in parser.parse_args().primes or PRIMES:
        run(prime)
