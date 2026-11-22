#!/usr/bin/env python3
"""Check the eighth-rate factor allocations immediately below and at 5n/8."""
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
def price(total, heads, b, agreements, cutoff):
    weight = PRIMARY[0] * agreements - 1 - (total - b) * DEGREE
    m = COMPANION[2] - heads
    if b == 1 or weight < b * DEGREE or m < b:
        return cutoff
    return max(cutoff, tangent_cap(b, m, weight, agreements, DEGREE))


def residuals(heads, agreements, cutoff):
    for total in range(heads, PRIMARY[1] + 1):
        for degrees in partitions(total - heads):
            remaining = PRIMARY[2] + sum(price(total, heads, b, agreements, cutoff) for b in degrees)
            yield remaining, degrees


def next_count():
    """Every allocation at exactly five eighths outside the exceptional quartet."""
    errors = ERRORS + 1
    agreements = N - errors
    cutoff = max(1 + errors // 8192, 1 + PRIMARY[2] * COMPANION[1] + PRIMARY[1] * COMPANION[2])
    floor = agreements - 8191
    ranks = tuple(surplus(shape, agreements, DEGREE) for shape in (PRIMARY, COMPANION))
    require(ranks == (44200, 805345446) and cutoff == 81921, "successor interpolation")
    m = COMPANION[2]
    require(agreements - m*N//cutoff - 3*(m*N//(cutoff-m)) > DEGREE, "successor identity test")
    require(errors//cutoff == 8191 and agreements**2 > N*DEGREE, "successor core and Johnson bounds")
    require(15*floor > 3*N+20*DEGREE and 13*floor > 3*N+13*DEGREE, "successor rich geometry")
    def head_price(deficit):
        return 1 + errors // deficit

    four_ordinary = max(2*head_price(1)+2*head_price(2), 3*head_price(1)+head_price(6))
    four_with_triple = max(1+3*(N-(3*floor-3*DEGREE))+head_price(1),
                           3*head_price(1)+head_price(3)-(floor-2*DEGREE))
    require((four_ordinary, four_with_triple) == (2125114030, 2102752598), "successor quartet caps")
    best = []
    checked = 0
    for j in range(PRIMARY[1]+1):
        head = j*head_price(1)
        if j >= 4:
            den = floor+(j-1)*DEGREE
            union = (j*floor**2+den-1)//den
            head = min(head, j*N-(j-1)*union)
        if j == 4:
            head = max(head, four_ordinary, four_with_triple)
        if j == 5:
            head = max(head, 2058021547)  # EighthFourPlusOne
        rows = list(residuals(j, agreements, cutoff))
        checked += len(rows)
        best.append((head + max(rows)[0], max(rows)))
    require(checked == 3370 and max(best)[0] <= 2*N, "every ordinary successor allocation")
    require(best[4][1] == (20607410, (12,)), "successor four-head residual")
    print("At five eighths,", checked, "allocations outside the exceptional quartet fit;",
          "maximum", max(best)[0], "and quartet residual", best[4][1][0])


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
        for remaining, degrees in residuals(j, AGREEMENTS, CUTOFF):
            count = head + remaining
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
    next_count()
