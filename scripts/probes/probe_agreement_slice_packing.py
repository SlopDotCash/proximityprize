#!/usr/bin/env python3
"""Check the agreement slice certificates and constant-weight obstructions."""

from itertools import combinations
from math import comb

PRIME = 126205134105047729256068842055334737587878534445324289139206048206460929
BUDGET = PRIME // 2**128

# n, dimension, agreements at upper bound, sample size, selected sample sites,
# local multiplicity, last support-color obstruction, last greedy obstruction.
CASES = (
    (128, 64, 67, 61, 2, 31, 66, 65),
    (1024, 512, 702, 131, 31, 363, 600, 658),
    (1024, 256, 479, 389, 269, 479, 338, 409),
    (1024, 128, 315, 128, 98, 320, 186, 238),
    (1024, 64, 191, 58, 50, 187, 99, 123),
)


def conflicts(n, k, t):
    """Number of t-sets meeting a fixed t-set in at least k sites."""
    return sum(comb(t, j) * comb(n - t, j) for j in range(min(t - k, n - t) + 1))


def main():
    # Compare the sphere formula and two-block row counts to direct enumeration.
    for n in range(3, 10):
        for t in range(2, n):
            subsets = tuple(map(frozenset, combinations(range(n), t)))
            for k in range(1, t + 1):
                degree = sum(len(subsets[0] & other) >= k for other in subsets)
                assert degree == conflicts(n, k, t)
            for w in range(1, n):
                samples = tuple(map(frozenset, combinations(range(n), w)))
                for a in range(max(0, t + w - n), min(w, t) + 1):
                    count = sum(len(subsets[0] & sample) == a for sample in samples)
                    assert count == comb(t, a) * comb(n - t, w - a)

    for n, k, t, w, a, local, colors, greedy in CASES:
        s, z = k - 1, n - w
        gap = a * a * z + (t - a)**2 * w - s * w * z
        assert gap > 0 and (t - s) * w * z // gap == local
        upper = local * comb(n, w) // (comb(t, a) * comb(n - t, w - a))
        assert upper <= BUDGET
        q = 131 if n == 128 else 1031
        assert comb(n, colors) > BUDGET * q**(colors - k)
        assert comb(n, colors + 1) <= BUDGET * q**(colors + 1 - k)
        assert comb(n, greedy) > BUDGET * conflicts(n, k, greedy)
        assert comb(n, greedy + 1) <= BUDGET * conflicts(n, k, greedy + 1)
        print(f"n={n} k={k} agreement={t} list≤{upper} "
              f"support obstructions at {colors} (color), {greedy} (greedy)")


if __name__ == "__main__":
    main()
