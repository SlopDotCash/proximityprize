#!/usr/bin/env python3
"""Exact controls for the dyadic signed norm, four-center coefficients and the degree-seven algebra."""
from itertools import combinations, product

from probe_linear_contact_quotient import require


def folded(m, terms):
    half = m//2
    result = [0]*half
    for i, coefficient in terms:
        i %= m
        result[i % half] += coefficient if i < half else -coefficient
    return result


def norm(vector):
    return sum(map(abs, vector))


def check_norm():
    m = 16
    subsets = [s for d in range(6) for s in combinations(range(m), d)]
    checked = 0
    small = [s for d in range(4) for s in combinations(range(m), d)]
    for s in subsets[::13]:
        vec = folded(m, [(v, 1) for v in s])
        require(norm(vec) % 2 == len(s) % 2, 'internal pairs leave parity unchanged')
        for a in range(m):
            for sign in (-1, 1):
                transformed = folded(m, [(a+sign*i, 1) for i in s])
                require(norm(transformed) == norm(vec), 'shift and conjugate norm')
        for t in small:
            if set(s).isdisjoint(t):
                tvec = folded(m, [(v, 1) for v in t])
                require(norm([x-y for x, y in zip(vec, tvec)]) == norm(vec)+norm(tvec),
                        'disjoint differences do not cancel')
                checked += 1
    for delta in product(range(-9, 10, 2), repeat=3):
        require(any(delta[j]+delta[k] for j, k in combinations(range(3), 2)),
                'odd norms cannot cancel in every pair')
    return checked


def check_four_roots():
    # Work at an exact finite specialization of the dyadic unit circle.
    # Conjugates below use inversion on the roots before any summation.
    p = 65537
    m = 32
    z = pow(3, (p-1)//m, p)
    powers = [pow(z, i, p) for i in range(m)]
    checks = 0
    for a in range(1, m, 2):
        for b in [None, *range(1, m, 2)]:
            if a == b:
                continue
            lead = (powers[-a]- (powers[-b] if b is not None else 0)) % p
            constant = (powers[a]-(powers[b] if b is not None else 0)) % p
            ratio = constant*pow(lead, -1, p) % p
            expect = powers[2*a % m] if b is None else -powers[(a+b) % m] % p
            require(ratio == expect, 'signed single or double minority-pair coefficient')
            for three in ((0, 2, 6), (1, 5, 9), (3, 7, 15)):
                fourth = ratio*pow(__import__('math').prod(powers[j] for j in three), -1, p) % p
                nodes = [powers[j] for j in three]+[fourth]
                c = (-lead*sum(nodes)) % p
                cbar = (-constant*sum(pow(v, -1, p) for v in nodes)) % p
                middle = lead*sum(x*y for x, y in combinations(nodes, 2)) % p
                require(all((lead*v**4+c*v**3+middle*v**2+cbar*v+constant) % p == 0 for v in nodes),
                        'virtual root, cubic coefficient and signs')
                checks += 1
    return checks


def check_circle():
    # Check the two possible values of U for r of order >2 using exact
    # coefficient vectors, retaining multiplicity when r and r^-1 coincide.
    m = 64
    for r in range(1, m):
        signed_r = folded(m, [(r, 1), (-r, 1)])
        for z_j in range(m):
            # Normalize z to one. z_j = 1-r*U and z_k = 1-U/r.
            U = folded(m, [(-r, 1), (z_j-r, -1)])
            z_k = folded(m, [(0, 1), (-2*r, -1), (z_j-2*r, 1)])
            if norm(z_k) == 1 and r != m//2:
                require(not any(U) or U == signed_r, 'two-circle alternatives')
                if any(U):
                    require(z_j == (2*r+m//2) % m, 'virtual root -z*r²')
                    require(z_k == folded(m, [(m//2-2*r, 1)]), 'virtual root -z/r²')
    for centers in combinations(range(m), 3):
        for z in range(m):
            v = folded(m, [(z, 2)]+[(t, 1) for t in centers])
            if norm(v) == 1:
                require(folded(m, [(z, 1)]+[(t, 1) for t in centers]) == [0]*(m//2),
                        'r=-1 case with distinct light roots')
    for j in range(m):
        for k in range(m):
            if j == k:
                continue
            for z in range(m):
                jr, kr = (z+k-j) % m, (z+j-k) % m
                left = folded(m, [(j+jr, 1), (j+z, 1)])
                right = folded(m, [(k+kr, 1), (k+z, 1)])
                require(left == right, 'crossed pair assignment')


if __name__ == '__main__':
    count = check_norm()
    quartics = check_four_roots()
    check_circle()
    print(f'{count} disjoint signed-norm checks; {quartics} exact virtual-root quartics.')
    print('Checked the crossed pairs, the two-circle alternatives and the r=-1 multiplicity case.')
