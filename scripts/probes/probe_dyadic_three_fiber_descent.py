#!/usr/bin/env python3
"""Check the two-shell conjugation and Fourier identities in exact dyadic test fields."""
from itertools import combinations
from math import prod

from probe_linear_contact_quotient import require


def check_shells(n):
    p = 65537
    m = n//2
    zeta = pow(3, (p-1)//n, p)
    theta = zeta*zeta % p
    require(pow(zeta, n//2, p) == p-1, 'primitive dyadic grid')

    # The toy supports have both singleton and paired contributions, including
    # an intact orbit in one support and a non-invariant pair in the other.
    pos_even = {0, 1, 2, 5, m//2+1}
    neg_even = {3, 4, 6, 7, m//2+3}
    pos_pair = {1, 1+m//2}
    neg_pair = {3}
    u = [int(i in pos_even)-int(i in neg_even) for i in range(m)]
    q = [int(i in pos_pair)-int(i in neg_pair) for i in range(m)]
    v = [(u[i]-u[(i+m//2) % m])*(i % 2) for i in range(m)]
    w = [(q[i]-q[(i+m//2) % m])*(i % 2) for i in range(m)]
    require(any(v) and any(w), 'both shell differences tested')
    powers = [pow(theta, i, p) for i in range(m)]

    def value(y, root):
        return (prod(pow((y-pow(root, i, p)) % p, u[i], p) for i in range(m) if u[i])
                * prod(pow((y*y-pow(root, i, p)) % p, q[i], p) for i in range(m) if q[i])) % p

    def transform(sequence, k):
        return sum(a*powers[-k*i % m] for i, a in enumerate(sequence)) % p

    for j in range(0, m, 2):
        if u[j]:
            continue
        ratio = value(powers[j], theta)*pow(value(powers[j], -theta), -1, p) % p
        combined = [(v[(j+i) % m]+w[(2*j+i) % m]) for i in range(m)]
        formal_value = prod(pow((1-powers[i]) % p, e, p) for i, e in enumerate(combined) if e) % p
        require(ratio == formal_value, 'conjugation quotient and doubled displacement')
        F = [combined[i]+combined[-i % m] for i in range(m)]
        for k in range(m):
            rhs = (powers[k*j % m]*transform(v, k)+powers[-k*j % m]*transform(v, -k)
                   +powers[2*k*j % m]*transform(w, k)+powers[-2*k*j % m]*transform(w, -k))
            require(transform(F, k) == rhs % p, 'Fourier signs and doubled frequency')
            if k % 2 == 0:
                require(transform(v, k) == transform(w, k) == 0, 'even frequency vanishing')

    # Over this exact test field, evaluate [z^-2,z^-1,1,z,z²]. Clearing the
    # common factor z^-2 makes the determinant the ordinary Vandermonde.
    five_sets = list(combinations(range(0, min(m, 32), 2), 5))
    for k in range(1, m, 2):
        for centers in five_sets:
            nodes = [powers[k*j % m] for j in centers]
            determinant = prod(b-a for i, a in enumerate(nodes) for b in nodes[i+1:]) % p
            require(determinant != 0, 'five distinct nodes at each odd frequency')
    return len(five_sets)*(m//2)


def parity_options():
    for degree in range(11, 64):
        low_high = [0, 1, 2, degree-2, degree-1, degree]
        for counts in __import__('itertools').product(low_high, repeat=3):
            # Each full test with three sites on a parity forces antipodal
            # closure on the opposite parity in both other supports.
            closures = [[False, False] for _ in range(3)]
            for i, odd in enumerate(counts):
                for j in range(3):
                    if i == j:
                        continue
                    if degree-odd >= 3:
                        closures[j][1] = True
                    if odd >= 3:
                        closures[j][0] = True
            if sum(all(c) for c in closures) >= 2:
                continue
            minority = counts if sum(x <= 2 for x in counts) >= 2 else [degree-x for x in counts]
            require(max(minority) <= 2, 'only the common majority case can remain')
            require(all((degree-x+1)//2 >= 5 for x in minority), 'five sites in one mod-four class')


if __name__ == '__main__':
    checks = sum(check_shells(n) for n in (32, 64, 128))
    parity_options()
    d = (2**28-2, 2**28-1, 2**28+1)
    require(all((e//(e & -e)) >= 11 for e in d), 'production odd parts')
    print(f'Conjugation and Fourier formulas checked on three grids; {checks} Vandermonde tests.')
    print(f'Production-shaped degrees {d} all have odd part at least eleven.')
