#!/usr/bin/env python3
"""Verify the rational data certifying a real spectrum with five prescribed moments."""

from fractions import Fraction
import sys


def baseline(n):
    shift = Fraction(1, 2700)
    weights = (522, -1755, 2540, -1980, 810, -137)
    for center, multiplier in ((0, 6), (Fraction(n, 2), 32), (n, 7)):
        for offset, weight in enumerate(weights, start=1):
            coefficient = -multiplier * weight
            value = center - offset * shift
            yield abs(coefficient), value if coefficient > 0 else -value


def verify(n, p):
    assert (p - 1) % n == 0
    k = (p - 1) // n
    atoms = tuple(baseline(n))
    sums = [sum(count * value**r for count, value in atoms) for r in range(6)]
    assert sums[0] == 348480
    assert [sums[r] for r in (1, 3, 5)] == [-1, -n**2, -n**4]
    maximum = max(abs(value) for _, value in atoms)
    assert maximum == n - Fraction(1, 2700)
    pairs = (k - int(sums[0])) // 2
    selected = k // 16
    assert 0 < selected < pairs
    second = (p - n - sums[2]) / 2
    fourth = (3*p*(n-1) - n**3 - sums[4]) / 2
    low = second**2 / pairs
    high = second**2 / selected
    t_squared = (fourth - low) / (high - low)
    assert 0 <= t_squared <= 1
    assert second / selected <= maximum**2
    assert k - sums[0] - 2*pairs in (0, 1)
    print(f"n={n} p={p} entries={k} max={maximum} baseline={sums[0]}")


if __name__ == "__main__":
    if len(sys.argv) == 3:
        verify(*(int(value, 0) for value in sys.argv[1:]))
    else:
        n = 1 << 30
        # The endpoints cover the sparse band with integral coset counts.
        for p in (2**158 + 1, 2**159 - n + 1):
            verify(n, p)
