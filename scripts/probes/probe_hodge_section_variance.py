#!/usr/bin/env python3
"""Exact arithmetic for the general-multiplicity Hodge bound at half rate."""
from itertools import combinations_with_replacement

N = 2**30
D = N // 2 - 1
E = 298_250_000
T = N - E
OUTER = (6, 8, 32_521)
SECOND = (12, 17, 98)


def check(test, message):
    if not test:
        raise ValueError(message)


def interpolation(orders):
    r, v, s = orders
    variables = sum((s - j + 1) * max(0, r * T - D * j) for j in range(v + 1))
    equations = N * sum((r - j) * (s + 1 - j) for j in range(r))
    return variables - equations


def section_bound(b):
    m = SECOND[2]
    weight = OUTER[0] * T - 1
    bx = (2 * b - 2) * m - b * (b - 1) + 1
    bz = (2 * b - 2) * weight - b * (b - 1) * D + 1
    cost = (8 * m * b + 2) * bx * bz + 2 * m * N + (N - D) * (m + 1)
    return bx + cost // (T - D)


def main():
    surpluses = [interpolation(orders) for orders in (OUTER, SECOND)]
    check(min(surpluses) > 0, "outer interpolation")
    bmax, scalar_cap = OUTER[1:]
    small = bmax * SECOND[2] + SECOND[1] * scalar_cap
    caps = [0, E + 1] + [section_bound(b) for b in range(2, bmax + 1)]
    check(small < min(caps[1:]), "common-factor threshold")
    # For a value-linear factor of total degree <=98, retain 99 labels with fewest
    # identity-site misses. Each triple meets on >d sites and lies on one head.
    check(T - 98 * N // (E + 1) - 3 * (98 * N // (E - 98)) > D, "affine head")
    # Assign each selected label to one factor, including points on intersections.
    partitions = [p for k in range(1, bmax + 1)
                  for p in combinations_with_replacement(range(1, bmax + 1), k)
                  if sum(p) <= bmax]
    over = [p for p in partitions if sum(caps[b] for b in p) > 2 * N]
    check(over == [(1,) * bmax], "factor allocation")
    # An overpopulation of eight linear factors makes every factor a head.
    floor = 2 * N + 1 - 7 * (E + 1)
    check(floor > small, "small factors")
    check(T - 98 * N // floor - 3 * (98 * N // (floor - 98)) > D, "rich heads")
    fresh = E // (floor - 1)
    core = T - fresh
    check(3 * core > N + 2 * D, "collinearity of the eight heads")
    holes = N - 2 * core + D
    check(N + 7 * holes <= 2 * N, "uncovered sites")
    print("interpolation surpluses", surpluses, "common-factor threshold", small)
    print("factor caps", caps[1:], "exceptional partition", over[0])
    print("head population floor", floor, "core floor", core, "uncovered sites at most", holes)
    print("first failing error count at least", E + 1)


if __name__ == "__main__":
    main()
