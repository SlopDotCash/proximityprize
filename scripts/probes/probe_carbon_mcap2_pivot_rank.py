#!/usr/bin/env python3
"""Exact-integer check of the mixed-jet room radii at the two second-prime Johnson pivots
(CarbonMCAP2PivotRank.lean).  Runs in well under a second."""
import random

N = 2**30
CASES = {
    'half': (2**29 - 1, 314_491_699, 110_255_990),
    'quarter': (2**28 - 1, 536_870_913, 72_057_593_769_492_479),
}


def room(r, d, t, delta):
    """Quadratic room condition 4 r^2 delta + d^2 + 4 r d^2 <= 4 r d t."""
    return 4 * r * r * delta + d * d + 4 * r * d * d <= 4 * r * d * t


def surplus(r, v, s, d, t):
    cols = sum((s + 1 - j) * max(0, r * t - j * d) for j in range(v + 1))
    rows = N * sum((r - j) * (s + 1 - j) for j in range(r))
    return cols - rows


def main():
    for name, (d, e, radius) in CASES.items():
        t = N - e
        delta = t * t - N * d
        assert 2 * t <= N + d and d <= t and delta + 2 * t * d <= t * t + d * d
        assert room(1, d, t, delta) and room(radius, d, t, delta)
        assert not room(radius + 1, d, t, delta)
        # Spot-check the no-room conclusion on small shapes (cheap brute force).
        rng = random.Random(0)
        for _ in range(200):
            r = rng.randint(1, 40)
            v = rng.randint(0, 60)
            s = rng.randint(r - 1, 80)
            assert surplus(r, v, s, d, t) <= 0, (name, r, v, s)
        print(f'{name}: t={t:,}, t^2-nd={delta:,}, room radius={radius:,} (exact endpoint)')
    # Prefix identity on random integers.
    rng = random.Random(1)
    for _ in range(500):
        n, d, t, r, l = (rng.randint(-60, 60) for _ in range(5))
        b = r * (r + 1)
        lhs = 4 * r * (b * d * (2 * l * r * t - d * l * (l - 1) - n * b))
        rhs = -(r * (r + 1)**2 * (4 * r * r * (n * d - t * t) + 4 * r * d * t - 4 * r * d * d - d * d)
                + r * ((2 * r * ((r + 1) * t - l * d) - (r + 1) * d)**2 + 4 * r * (l - r - 1)**2 * d * d))
        assert lhs == rhs
    print('prefix identity verified')


if __name__ == '__main__':
    main()
