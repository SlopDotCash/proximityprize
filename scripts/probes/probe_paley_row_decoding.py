#!/usr/bin/env python3
"""Exhaust the binary Paley row decoding inequalities over F_3, F_5, F_7."""

from itertools import combinations


def subsets(mask):
    subset = mask
    while True:
        yield subset
        if not subset:
            return
        subset = (subset - 1) & mask


def separator(words, p):
    """Choose the site that leaves the fewest currently unresolved label pairs."""
    pairs = list(combinations(words, 2))
    mask = 0
    while pairs:
        site = min(range(p), key=lambda x: sum(not ((u ^ v) >> x & 1) for u, v in pairs))
        next_pairs = [(u, v) for u, v in pairs if not ((u ^ v) >> site & 1)]
        assert 2 * p * len(next_pairs) <= (p + 1) * len(pairs)
        mask |= 1 << site
        pairs = next_pairs
    assert len({word & mask for word in words}) == p
    return mask


def check_prime(p):
    squares = {x * x % p for x in range(1, p)}
    chi = [0] + [1 if x in squares else -1 for x in range(1, p)]
    words = [sum(1 << x for x in range(p) if chi[(x + b) % p] >= 0) for b in range(p)]
    full = (1 << p) - 1
    for b, c in combinations(range(p), 2):
        assert sum(chi[(x + b) % p] * chi[(x + c) % p] for x in range(p)) == -1
        assert 2 * (words[b] ^ words[c]).bit_count() >= p - 1
    # The affine and constant word lines have different quadratic sums over all sites.
    assert all(sum(chi[(x + b) % p] for x in range(p)) == 0 for b in range(p))
    assert sum(p * chi[b] for b in squares) == p * len(squares)
    distinguish = separator(words, p)
    k = 0
    while 3**k < p**2 * 2**k:
        k += 1
    assert distinguish.bit_count() <= k

    # Precompute each character rectangle sum with a single shift.
    rows = [[sum(chi[(x + b) % p] for x in range(p) if mask >> x & 1)
             for b in range(p)] for mask in range(full + 1)]
    worst_lists = {}
    ball_count = 0
    for mask in range(full + 1):
        n = mask.bit_count()
        canonical = {word & mask: b for b, word in enumerate(words)}
        worst = [0] * (n + 2)
        for center in subsets(mask):
            correlations = {b: n - 2 * (word ^ center).bit_count() for word, b in canonical.items()}
            signed = [rows[center][b] - rows[mask ^ center][b] for b in range(p)]
            assert sum(s * s for s in signed) == p * n - (2 * center.bit_count() - n)**2
            for t in range(n + 2):
                labels = [b for b, correlation in correlations.items() if correlation >= t]
                m = len(labels)
                worst[t] = max(worst[t], m)
                assert (t - 1) * m <= sum(signed[b] for b in labels)
                if t > 1:
                    assert (t - 1)**2 * m <= p * n
                ball_count += 1
        worst_lists[mask] = worst

    rectangle_count = 0
    for mask in range(full + 1):
        n = mask.bit_count()
        extended = mask | distinguish
        length = extended.bit_count()
        extra = length - n
        assert len({word & extended for word in words}) == p
        for b, word in enumerate(words):
            correlation = 2 * (word & extended).bit_count() - length
            assert abs(correlation - rows[mask][b]) <= extra + 1
        for labels in range(full + 1):
            m = labels.bit_count()
            discrepancy = abs(sum(rows[mask][b] for b in range(p) if labels >> b & 1))
            for t, cap in enumerate(worst_lists[extended]):
                assert discrepancy <= (t + extra + 1) * m + n * cap
                rectangle_count += 1
    print(f"p={p} separator_size={distinguish.bit_count()} "
          f"balls={ball_count} rectangle_thresholds={rectangle_count}")


if __name__ == "__main__":
    for prime in (3, 5, 7):
        check_prime(prime)
