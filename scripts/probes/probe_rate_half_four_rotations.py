#!/usr/bin/env python3
"""Enumerate the two generalized Vandermonde obstructions for four 32-fibre rotations."""

from itertools import combinations, product

from probe_rate_half_mobius_seams import G, N, P, require


def count_configurations():
    w = pow(G, N // 32, P)
    require(pow(w, 32, P) == 1 and pow(w, 16, P) != 1, 'order is not 32')
    roots = [pow(w, i, P) for i in range(32)]
    for length, expected in ((6, 28672), (5, 14336)):
        configurations = 0
        for orbits in combinations(range(8), length):
            for rotations in product(range(4), repeat=length - 1):
                # Multiplying every root by the same fourth root preserves each
                # elementary-symmetric zero and allows the first rotation to be zero.
                exponents = (orbits[0], *(i + 8*r for i, r in zip(orbits[1:], rotations)))
                e1 = e2 = e3 = 0
                for i in exponents:
                    z = roots[i]
                    e1, e2, e3 = (e1+z) % P, (e2+z*e1) % P, (e3+z*e2) % P
                violation = e3 == 0 if length == 6 else e2 == 0 and e3 == 0
                require(not violation, f'unexpected exceptional point set {exponents}')
                configurations += 1
        require(configurations == expected, 'incomplete enumeration')
        print(f'{length} exceptional representatives: {configurations} configurations, no admissible set')


if __name__ == '__main__':
    count_configurations()
