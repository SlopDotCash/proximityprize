#!/usr/bin/env python3
"""Certify the characteristic-zero degeneracy of the nonfaithful affine census."""

import argparse
from itertools import combinations, permutations
from math import gcd, isqrt
from pathlib import Path

from probe_quarter_sixteen_splines import nullspace

EDGES = tuple(combinations(range(4), 2))
TRIANGLES = tuple(combinations(range(4), 3))
P = 2**64 - 2**32 + 1


def check_prime():
    factors = [2, 3, 5, 17, 257, 65537]
    assert P-1 == 2**32 * 3 * 5 * 17 * 257 * 65537
    assert all(all(q % d for d in range(2, isqrt(q)+1)) for q in factors)
    # These conditions give a unit of order P-1 modulo P, proving primality.
    assert pow(7, P-1, P) == 1
    assert all(gcd(pow(7, (P-1)//q, P)-1, P) == 1 for q in factors)


def orbit(masks):
    sites = [[i for i in range(32) if m >> i & 1] for m in masks]
    labels = [tuple(EDGES.index(tuple(sorted((perm[a], perm[b])))) for a, b in EDGES)
              for perm in permutations(range(4))]
    for u in range(1, 32, 2):
        scaled = [sum(1 << ((u*i) % 32) for i in block) for block in sites]
        for b in range(32):
            shift = [((m << b) | (m >> (32-b))) & (2**32-1) for m in scaled]
            for perm in labels:
                yield tuple(shift[e] for e in perm)


def forced_triangle(masks):
    zeta = pow(7, (P-1)//32, P)
    assert pow(zeta, 16, P) == P-1
    common = set(TRIANGLES)
    for u in range(1, 32, 2):
        z = pow(zeta, u, P)
        rows = []
        for mask, (a, b) in zip(masks, EDGES):
            for i in range(32):
                if mask >> i & 1:
                    row = [0]*24
                    for h, sign in ((a, 1), (b, -1)):
                        if h:
                            for d in range(8):
                                row[(h-1)*8+d] = sign * pow(z, (i*d) % 32, P) % P
                    rows.append(row)
        kernel = nullspace(rows, P)
        assert len(kernel) == 2
        # Head zero was translated away. At X=0 the other head values are
        # exactly the first coefficient of each of the remaining three blocks.
        x, y = ([0] + [v[j] for j in (0, 8, 16)] for v in kernel)
        common &= {(a, b, c) for a, b, c in TRIANGLES
                   if ((x[b]-x[a])*(y[c]-y[a]) - (x[c]-x[a])*(y[b]-y[a])) % P == 0}
    assert common
    return min(common)


def verify(file):
    check_prime()
    masks = set()
    total = cases = entries = 0
    for line in file.read_text().splitlines():
        parts = line.split()
        if parts and parts[0] == 'layout':
            layout = tuple(map(int, parts[1:]))
            assert len(layout) == 6 and sum(m.bit_count() for m in layout) == 28
            masks.add(layout)
            entries += 1
        else:
            assert len(parts) >= 5 and parts[0] in ('cyclic', 'Klein') and parts[-2] == 'survivors'
            total += int(parts[-1])
            cases += 1
    assert cases == 22 and entries == total == 142 and len(masks) == 125
    classes = 0
    while masks:
        representative = min(masks)
        triangle = forced_triangle(representative)
        print(f'{representative} forces a collinear triple {triangle} at zero')
        masks.difference_update(orbit(representative))
        classes += 1
    assert classes == 16
    print(f'Certified {classes} affine and vertex orbits from {entries} representative records.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('census', type=Path, help='output of the affine probe with --nonfaithful')
    verify(parser.parse_args().census)
