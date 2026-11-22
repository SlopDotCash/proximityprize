#!/usr/bin/env python3
"""Bound locator lists from a fixed product and per-coordinate fresh-match cap."""

from collections import Counter
from functools import cache
from itertools import combinations
from math import comb


@cache
def overlap_layers(order, degree, selected):
    """Caps on the number of supports intersecting selected labels in j sites."""
    outside = order - selected
    layers = []
    for j in range(min(selected, degree), max(0, degree - outside) - 1, -1):
        k = degree - j
        mass = comb(selected, j) * comb(outside, k)
        # For a prescribed product, a deleted root is recovered from all the others.
        if j:
            mass = min(mass, comb(selected, j - 1) * comb(outside, k) // j)
        if k:
            mass = min(mass, comb(selected, j) * comb(outside, k - 1) // k)
        layers.append((j, mass))
    return tuple(layers)


def top_overlap(order, degree, selected, words):
    """Fill the largest overlap layers first for an upper bound on total overlap."""
    total = 0
    for overlap, mass in overlap_layers(order, degree, selected):
        take = min(mass, words)
        total += overlap * take
        words -= take
        if words == 0:
            break
    return total


def list_cap(order, degree, fiber_size, agreement, fresh_cap):
    """List upper bound for a fixed root product and at most fiber_size-1 zeros."""
    if not (0 <= degree < order and fiber_size > 0 and fresh_cap > 0):
        raise ValueError("invalid locator parameters")
    if not ((degree + 1) * fiber_size - 1 < agreement <= order * fiber_size):
        raise ValueError("agreement must exceed the root and multiplier baseline")
    if degree == 0:
        return 1
    # The same one-root deletion bounds the total number at the prescribed product.
    support_cap = comb(order, degree - 1) // degree

    def excluded(words):
        if words > support_cap:
            return True
        if words <= fresh_cap:
            return False
        required = words * (agreement - fiber_size + 1)
        for selected in range(order + 1):
            available = ((order - 1 - selected) * fiber_size + 1) * fresh_cap
            available += fiber_size * top_overlap(order, degree, selected, words)
            if required <= available:
                return False
        return True

    low, high = 0, support_cap + 1
    while high - low > 1:
        middle = (high + low) // 2
        if excluded(middle):
            high = middle
        else:
            low = middle
    assert excluded(low + 1)
    return low


def small_control():
    # On the order-eight subgroup a root product is the sum of exponents modulo 8.
    # Visit every product, selected-label set, and list size in degrees 0..4.
    order = 8
    subsets = tuple(frozenset(i for i in range(order) if (mask >> i) & 1)
                    for mask in range(1 << order))
    for degree in range(5):
        for product in range(order):
            supports = [subset for subset in subsets
                        if len(subset) == degree and sum(subset) % order == product]
            for selected in subsets:
                overlaps = sorted((len(s & selected) for s in supports), reverse=True)
                actual = Counter(overlaps)
                layers = overlap_layers(order, degree, len(selected))
                assert all(actual[j] <= bound for j, bound in layers)
                assert sum(actual[j] for j, _ in layers) == len(supports)
                for words in range(1, len(supports) + 1):
                    assert sum(overlaps[:words]) <= top_overlap(order, degree, len(selected), words)
            # Independently compute each actual list's positive occupancy excess.
            for words in range(1, len(supports) + 1):
                for family in combinations(supports, words):
                    occupancies = [sum(i in support for support in family) for i in range(order)]
                    for fresh_cap in (1, 2):
                        actual = sum(max(0, n - fresh_cap) for n in occupancies)
                        bound = max(top_overlap(order, degree, selected, words) - fresh_cap * selected
                                    for selected in range(order + 1))
                        assert actual <= bound


def main():
    small_control()
    agreement = 20 * (1 << 22) - 1
    cases = [
        (128, (1, 1, 1, 2, 6, 57, 1206, 19022, 160036),
         (1, 1, 15, 37, 133, 1489, 37788, 798924, 12322772), 13161160),
        (256, (1, 1, 1, 2, 6, 108, 4590, 155998, 2562572, 72606206),
         (1, 1, 13, 30, 96, 1788, 76662, 2645874, 45427412, 1332411487), 48151877),
    ]
    for order, fresh_caps, expected, total in cases:
        h = (1 << 30) // order
        caps = tuple(list_cap(order, m, h, agreement, c) for m, c in enumerate(fresh_caps))
        assert caps == expected and sum(caps[:9]) == total
        print(f"order {order} per-degree caps {caps}, total through eight {total}")
    degree18 = list_cap(256, 18, 1 << 22, agreement, 2830428)
    assert degree18 == 617033304
    print(f"order 256 degree 18 through eight unpaired roots {degree18}")


if __name__ == "__main__":
    main()
