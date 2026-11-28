#!/usr/bin/env python3
"""Certify ordered cross-ratio transfer on the two named dyadic subgroups."""
import argparse
from array import array
from itertools import permutations
from math import comb

PRIMES = (365375409332725729550921208179070755120141565953,
          730750818665451459101842416358141509841924915201)


def gap_orbits(n):
    """Cyclic gaps modulo rotations and reversal of an unordered four-set."""
    for a in range(1, n // 4 + 1):
        for b in range(a, n - 3*a + 1):
            for c in range(a, n - 2*a - b + 1):
                gaps = (a, b, c, n-a-b-c)
                orbit = {row[k:] + row[:k] for row in (gaps, gaps[::-1]) for k in range(4)}
                if gaps == min(orbit):
                    yield (a, a+b, a+b+c), len(orbit)


def first_accident(n, p):
    for seed in range(2, p):
        z = pow(seed, (p - 1) // n, p)
        if pow(z, n // 2, p) == p - 1:
            break
    else:
        raise ArithmeticError(f'no primitive {n}th root in characteristic {p}')
    roots = [pow(z, j, p) for j in range(n)]
    assert len(set(roots)) == n and pow(z, n, p) == 1
    diff = [[(x-y) % p for y in roots] for x in roots]
    inv = [[pow(v, -1, p) if v else 0 for v in row] for row in diff]

    def ratio(i, j, k):
        return ((diff[0][j]*inv[0][k] % p) * (diff[i][k]*inv[i][j] % p)) % p

    # The coefficient bound in the cleared equality is 32; base 64 is separating.
    modulus = 64**(n//2) + 1
    powers = [64**i for i in range(n//2)]
    powers += [-x for x in powers]

    def formal_ratio(i, j, k):
        return ((1-powers[j])*(powers[i]-powers[k]), (1-powers[k])*(powers[i]-powers[j]))

    # Store one packed representative per distinct residue. Tags only accelerate lookup;
    # every possible tag collision is resolved by recomputing the full finite-field ratio.
    bits = (comb(n-1, 3)*3//2 + 1).bit_length()
    size = 1 << bits
    mask = size-1
    words = array('I', [0]) * size
    tags = array('H', [0]) * size
    anchored = classes = occupied = repeated = 0
    for sites, orbit_size in gap_orbits(n):
        classes += 1
        anchored += orbit_size
        for i, j, k in permutations(sites):
            value = ratio(i, j, k)
            fingerprint = hash(value)
            slot = fingerprint & mask
            tag = (fingerprint >> bits) & 65535
            while words[slot]:
                if tags[slot] == tag:
                    pairs, kk = divmod(words[slot], n)
                    ii, jj = divmod(pairs, n)
                    if ratio(ii, jj, kk) == value:
                        a, b = formal_ratio(i, j, k)
                        c, d = formal_ratio(ii, jj, kk)
                        if (a*d-b*c) % modulus:
                            return (value, (0, ii, jj, kk), (0, i, j, k)), None
                        repeated += 1
                        break
                slot = (slot+1) & mask
            else:
                words[slot] = (i*n+j)*n+k
                tags[slot] = tag
                occupied += 1
    # Burnside check, independently counting 4-sets fixed by rotations and reflections.
    half = n // 2
    rotations = comb(n, 4) + comb(half, 2) + 2*(n//4)
    reflections = half * (comb(half, 2) + comb(half-1, 2) + half-1)
    assert classes * 2*n == rotations + reflections
    assert anchored == comb(n-1, 3) and occupied + repeated == 6*classes
    return None, (z, classes, occupied, repeated)


def six_matches(n, p, root):
    grid = [pow(root, j, p) for j in range(n)]
    stride = n//8
    a, b, c = [grid[i*stride] for i in (0, 1, 2)]
    A, B, C = [grid[i*stride] for i in (0, 1, 3)]
    targets = {x: i for i, x in enumerate(grid)}
    matches = []
    for i, x in enumerate(grid):
        u = (x-b)*(c-a)*(C-B) % p
        v = (x-a)*(c-b)*(C-A) % p
        if u != v:
            y = (u*A-v*B)*pow((u-v) % p, -1, p) % p
            if y in targets:
                matches.append((i, targets[y]))
    expected = [(0, 0), (1, 1), (2, 3), (3, 5), (4, 6), (6, 7)]
    assert matches == [(stride*x, stride*y) for x, y in expected]
    return matches


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, choices=(256, 512), default=512)
    args = parser.parse_args()
    accident, _ = first_accident(16, 17)
    assert accident == (12, (0, 4, 1, 2), (0, 1, 2, 5))
    print('Negative control at order 16 in characteristic 17:', accident, flush=True)
    for p in PRIMES:
        accident, counts = first_accident(args.order, p)
        if accident:
            raise ArithmeticError(f'nonlifting comparison at p={p}: {accident}')
        expected = {256: (345472, 2001387, 71445), 512: (2779904, 16389099, 290325)}
        assert counts[1:] == expected[args.order]
        print(f'p={p}, order={args.order}: root / orbits / distinct / repeated = {counts}', flush=True)
        print('Sharp matched exponent pairs:', six_matches(args.order, p, counts[0]), flush=True)


if __name__ == '__main__':
    main()
