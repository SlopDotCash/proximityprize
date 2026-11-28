"""Check the Fourier-width pencil bound and the support thresholds at the quarter successor."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd
from random import Random


def arithmetic():
    thresholds = {}
    for terms in range(5, 9):
        j = 0
        while (1 << j) * terms <= 20 ** (terms - 1):
            j += 1
        thresholds[terms] = j
    assert thresholds == {5: 15, 6: 20, 7: 24, 8: 28}
    n = 1 << 30
    d = n // 4 - 2
    for b in (1, 2):
        size, degree = n // b, d // b
        for terms in range(2, 11):
            assert size * terms > Fraction(1201, 100) ** (terms - 1)
        assert Fraction(200, 1201) < Fraction(degree, 3 * (size - 2 * degree))
    for odd_degree in (n // 4 - 1, n // 4 + 1):
        assert gcd(odd_degree, n) == 1
        assert Fraction(200, 1201) < Fraction(odd_degree, 3 * (n - 2 * odd_degree))
    print('All frequency thresholds and both full-fiber normalizations verified.')


def projective_pencils(p, dimensions):
    """All planes in coefficient space, using their unique reduced echelon bases."""
    for first, second in combinations(range(dimensions), 2):
        a, b = [0] * dimensions, [0] * dimensions
        a[first], b[second] = 1, 1
        free = [(a, j) for j in range(first + 1, dimensions) if j != second]
        free.extend((b, j) for j in range(second + 1, dimensions))
        for coeffs in product(range(p), repeat=len(free)):
            for (row, j), value in zip(free, coeffs):
                row[j] = value
            yield a, b


def coprime(a, b, p):
    a, b = a.copy(), b.copy()
    while b and b[-1] == 0:
        b.pop()
    while b:
        while len(a) >= len(b):
            c = a[-1] * pow(b[-1], -1, p) % p
            offset = len(a) - len(b)
            for j, v in enumerate(b):
                a[offset + j] = (a[offset + j] - c * v) % p
            while a and a[-1] == 0:
                a.pop()
        a, b = b, a
    return len(a) == 1


def width(freqs, multiplier, n):
    indices = sorted({f * multiplier % n for f in freqs})
    gaps = [b - a for a, b in zip(indices, indices[1:])]
    gaps.append(n + indices[0] - indices[-1])
    return n - max(gaps)


def check_pencil(a, b, p, sites):
    n = len(sites)
    freqs = [j for j, pair in enumerate(zip(a, b)) if any(pair)]
    m = max(freqs)
    if min(freqs) or gcd(*freqs) != 1 or not coprime(a, b, p):
        return False
    values = []
    for x in sites:
        top = sum(c * pow(x, j, p) for j, c in enumerate(a)) % p
        bottom = sum(c * pow(x, j, p) for j, c in enumerate(b)) % p
        assert top or bottom
        values.append(top * pow(bottom, -1, p) % p if bottom else p)
    totals = Counter(values)
    for u in range(1, n):
        g = gcd(u, n)
        t = n // g
        w = width(freqs, u, n)
        constants = Counter()
        for j in range(g):
            counts = Counter(values[j::g])
            if len(counts) == 1:
                constants.update(counts)
            else:
                assert g * max(counts.values()) <= w
        assert sum(constants.values()) <= 2 * t * (m // t)
        # Maximize the cleared inequality over every triple of targets.
        gains = sorted((n * h - (n - 3 * w) * constants[z]
                        for z, h in totals.items()), reverse=True)
        assert sum(gains[:3]) <= 3 * w * n
        if 3 * w < n:
            assert n * sum(sorted(totals.values(), reverse=True)[:3]) <= (
                2 * m * n + 3 * w * (n - 2 * m))
    return True


def finite_controls():
    checked = 0
    sites = [pow(3, j, 17) for j in range(16)]
    for a, b in projective_pencils(17, 3):
        checked += check_pencil(a, b, 17, sites)
    rng = Random(571)
    for n in (32, 64, 128):
        sites = [pow(3, j * 256 // n, 257) for j in range(n)]
        assert len(set(sites)) == n
        for _ in range(45):
            m = rng.randrange(3, n // 4)
            freqs = [0, m] + rng.sample(range(1, m), min(5, m - 1))
            a = [rng.randrange(257) if j in freqs else 0 for j in range(m + 1)]
            b = [rng.randrange(257) if j in freqs else 0 for j in range(m + 1)]
            checked += check_pencil(a, b, 257, sites)
        # A map with full constant cosets in the two selected polar fibers.
        h = n // 8
        a, b = [0] * (h + 2), [0] * (h + 2)
        a[0], a[h] = 256, 1
        b[1], b[h + 1] = 1, 1
        assert check_pencil(a, b, 257, sites)
        checked += 1
    print(f'Checked all multipliers and target triples on {checked} finite-field pencils.')


if __name__ == '__main__':
    arithmetic()
    finite_controls()
