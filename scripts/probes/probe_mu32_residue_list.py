#!/usr/bin/env python3
"""Check the residue-degree transfer, its high-extension census, and a quarter-rate witness."""
from math import isqrt

from probe_mu32_four_cubics import ZERO, multiply, root, subtract, value
from probe_mu32_quarter_witness import PAIR_CLASSES, SUPPORTS
from probe_mu32_ratio_norm import SCALE, log2_chords, maxima


def real_degree(p):
    """Orbit length of z + 1/z for a primitive 32nd root in characteristic p."""
    return next(j for j in range(1, 9) if pow(p, j, 32) in (1, 31))


def high_extensions():
    results = []
    # For e >= 13, p^13 <= p^e < 2^130 = 1024^13.
    for p in range(3, 1024, 2):
        if any(p % k == 0 for k in range(3, isqrt(p) + 1, 2)):
            continue
        e = 13
        while p**e < 3 * 2**128:
            e += 1
        if p**e < 4 * 2**128 and pow(p, e, 32) == 1:
            results.append((p, e))
    return results


def at_277(coefficients):
    # z^8=60 and 60^2=-1. All roots have order 32, hence degree eight.
    return tuple((coefficients[k] + 60 * coefficients[k + 8]) % 277 for k in range(8))


def check_quarter_center():
    a, b, c = [tuple(2 * j for j in support) for support in SUPPORTS]
    scales = (multiply(value(b, 8), value(c, 16)), multiply(value(a, 8), value(c, 16)),
              multiply(value(a, 16), value(b, 8)))
    heads = []
    center = []
    free = iter((0, 0, 1, 1, 2, 3))
    for j in range(32):
        locator = subtract(root(j), root(17))
        row = [at_277(ZERO)] + [
            at_277(multiply(locator, multiply(s, value(support, 2 * (j % 16)))))
            for support, s in zip((a, b, c), scales)]
        tag = '0123' if j == 17 else PAIR_CLASSES[j % 16]
        chosen = int(tag[0]) if tag else next(free)
        heads.append(row)
        center.append(row[chosen])
    assert next(free, None) is None
    words = list(zip(*heads))
    assert len(set(words)) == 4
    counts = [sum(v == w for v, w in zip(word, center)) for word in words]
    assert counts == [16, 16, 16, 16]
    return counts


def main():
    degrees = (5, 6, 7, 8)
    logs = log2_chords()
    bounds = [maxima(logs, shift, degrees) for shift in (1, 2, 4, 8)]
    largest = max(row[d] for d in degrees for row in bounds)
    assert largest == 130246 < 128 * SCALE
    assert high_extensions() == [(277, 16)]
    assert 60**2 % 277 == 276 and real_degree(277) == 8
    assert len({at_277(root(k)) for k in range(32)}) == 32
    assert 277**16 // 2**128 == 3 and 277**(2 * real_degree(277)) > 2**128
    # Frobenius inversion and an eligible ambient field outside this certificate.
    assert real_degree(31) == 1 and pow(31, 1, 32) != 1
    assert 1783**12 // 2**128 == 3 and pow(1783, 12, 32) == 1
    assert 1783**(2 * real_degree(1783)) < 2**128
    print('Largest scaled odd-norm exponent:', largest, '/', SCALE)
    print('All eligible (p,e) for e >= 13:', high_extensions())
    print('Four quarter-rate agreement counts over the degree-eight subfield:', check_quarter_center())


if __name__ == '__main__':
    main()
