#!/usr/bin/env python3
"""Check the two interpolants and every eighth-rate factor allocation at 5n/8-1."""
from functools import cache

from probe_tangent_head_windows import N, surplus, tangent_cap


ERRORS = 671_088_639
DEGREE = N // 8 - 1
AGREEMENTS = N - ERRORS
MIN_CORE = AGREEMENTS - 8191
PRIMARY = (6, 16, 335)
COMPANION = (9, 26, 128)
CUTOFF = max(1 + ERRORS // 8192, 1 + PRIMARY[2] * COMPANION[1] + PRIMARY[1] * COMPANION[2])


def require(test, message):
    if not test:
        raise ValueError(message)


def allowance(deficit):
    return 1 + ERRORS // deficit


def head_bound(count):
    if count <= 3:
        return count * allowance(1)
    denominator = MIN_CORE + (count - 1) * DEGREE
    covered = (count * MIN_CORE**2 + denominator - 1) // denominator
    collinear = min(count * allowance(1), count * N - (count - 1) * covered)
    if count == 4:
        split = max(3 * allowance(1) + allowance(6), 2 * allowance(1) + 2 * allowance(2))
        return max(collinear, split)
    if count == 5:
        line_union = 4 * MIN_CORE - 6 * DEGREE
        loss = MIN_CORE - 2 * DEGREE
        pair = 2 * allowance(1) - loss
        split = max(
            1 + 4 * (N - line_union) + allowance(1),  # constant line direction
            4 * N - 3 * line_union + allowance(3),   # transverse deficit >= 3
            pair + allowance(1) + 2 * allowance(7),  # transverse deficit 1, two saturated
            pair + allowance(2) + 2 * allowance(6),  # transverse deficit 2, two saturated
            2 * allowance(1) + allowance(2) + 2 * allowance(3),
        )
        return max(collinear, split)
    return collinear


@cache
def partitions(total, smallest=1):
    if total == 0:
        return [()]
    return [(b,) + tail for b in range(smallest, total + 1)
            for tail in partitions(total - b, b)]


@cache
def price(total, heads, b):
    weight = PRIMARY[0] * AGREEMENTS - 1 - (total - b) * DEGREE
    m = COMPANION[2] - heads
    if b == 1 or weight < b * DEGREE or m < b:
        return CUTOFF
    return max(CUTOFF, tangent_cap(b, m, weight, AGREEMENTS, DEGREE))


def main():
    ranks = tuple(surplus(shape, AGREEMENTS, DEGREE) for shape in (PRIMARY, COMPANION))
    require(min(ranks) > 0 and CUTOFF == 81920, "interpolation and cutoff")
    m = COMPANION[2]
    require(AGREEMENTS - m*N//CUTOFF - 3*(m*N//(CUTOFF-m)) > DEGREE, "identity sites")
    require(ERRORS//CUTOFF == 8191 and AGREEMENTS**2 > N * DEGREE, "core and Johnson bounds")
    require(15*MIN_CORE > 3*N + 20*DEGREE and 13*MIN_CORE > 3*N + 13*DEGREE, "five-head tests")
    require(4*AGREEMENTS - N - 4*DEGREE == 8, "exceptional quartet deficit")
    best = []
    checked = 0
    for j in range(PRIMARY[1] + 1):
        head = head_bound(j)
        candidates = []
        for total in range(j, PRIMARY[1] + 1):
            for degrees in partitions(total - j):
                count = PRIMARY[2] + head + sum(price(total, j, b) for b in degrees)
                candidates.append((count, degrees))
                require(count <= 2*N, (j, degrees, count))
                checked += 1
        best.append(max(candidates))
    worst, j = max((row, j) for j, row in enumerate(best))
    require((worst, j) == ((2_145_721_437, (12,)), 4), "worst allocation")
    print("Jet surpluses", *ranks, "with strict cutoff", CUTOFF)
    print("Four- and five-head counts including all other factors", best[4], best[5])
    print("Checked", checked, "allocations. Maximum", worst[0], "with", j, "rich heads.")


if __name__ == "__main__":
    main()
