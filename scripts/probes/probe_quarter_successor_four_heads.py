#!/usr/bin/env python3
"""Enumerate the small occupancy signatures left by a four-head successor failure."""

from itertools import combinations, combinations_with_replacement


def require(condition, message):
    if not condition:
        raise ValueError(message)


def examples(h):
    n, core, pair_cap = 4 * h, 3 * h - 2, 2 * h - 2
    heads = tuple(range(4))
    pairs = tuple(combinations(heads, 2))
    found = {}
    # One uncovered site and the incidence slack give singles + quadruples <= 1.
    for singles, quadruples in [(0, 0), (1, 0), (0, 1)]:
        doubles = 5 - 2 * singles + quadruples
        triples = n - 1 - singles - doubles - quadruples
        for lone in (heads if singles else (None,)):
            for assignment in combinations_with_replacement(pairs, doubles):
                # All core sizes are fixed. This determines each omitted-head triple class.
                omitted = tuple(
                    triples + sum(i in pair for pair in assignment) + (i == lone)
                    + quadruples - core for i in heads
                )
                if min(omitted) < 0 or sum(omitted) != triples:
                    continue
                overlap = tuple(
                    triples - omitted[i] - omitted[j] + assignment.count((i, j)) + quadruples
                    for i, j in pairs
                )
                if max(overlap) > pair_cap:
                    continue
                key = (singles, doubles, quadruples)
                residual_degree = 2 * pair_cap - (triples + 2 * quadruples)
                found.setdefault(key, (omitted, overlap, residual_degree))
    return found


def main():
    h = 2**28
    fits = examples(h)
    require({key: data[-1] for key, data in fits.items()} ==
            {(0, 5, 0): 2, (1, 3, 0): 1, (0, 6, 1): 2}, "occupancy profiles")
    for key, (omitted, overlaps, degree) in fits.items():
        print(f"singles/doubles/quadruples {key}, omitted triple classes {omitted}, "
              f"pair overlaps {overlaps}, residual degree <= {degree}")
    n, d = 4 * h, 2 * h - 1
    require((20 * d + 12 * n) // 30 + 1 == 787410671, "five-set threshold")
    require(n - 787410671 == 286331153, "four-list radius")
    require(16 * (3 * h - 2) > 12 * (2 * h - 3) + 6 * n, "direction degree")
    print("All three occupancy types satisfy the individual core and pair bounds.")


if __name__ == "__main__":
    main()
