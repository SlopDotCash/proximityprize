#!/usr/bin/env python3
"""Verify the six fully split polynomial differences construction in Z[z]/(z^8+1)."""
from itertools import combinations
from math import comb


N = 2**30
D = N // 8 - 1
T = 379625061
FIBER = N // 16
COMMON = FIBER - 1
RAYS = ((1, 2), (3, 4), (7, 9), (8, 9))


def check(condition, message):
    if not condition:
        raise ValueError(message)


def monomial(exponent, coefficient=1):
    entries = [0] * 8
    entries[exponent % 8] = (-1) ** (exponent // 8) * coefficient
    return tuple(entries)


def subtract(left, right):
    return tuple(a - b for a, b in zip(left, right))


def multiply(left, right):
    entries = [0] * 8
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            power = i + j
            entries[power % 8] += (-1) ** (power // 8) * a * b
    return tuple(entries)


def conjugate(element, power):
    entries = [0] * 8
    for i, coefficient in enumerate(element):
        exponent = i * power
        entries[exponent % 8] += (-1) ** (exponent // 8) * coefficient
    return tuple(entries)


def norm(element):
    result = monomial(0)
    for power in range(1, 16, 2):
        result = multiply(result, conjugate(element, power))
    check(not any(result[1:]), "field norm must be a rational integer")
    return result[0]


def check_dyadic_unit(element):
    value = abs(norm(element))
    check(value > 0 and value & (value - 1) == 0, "unexpected odd prime in norm")


def verify_heads():
    one, zero = monomial(0), monomial(0, 0)
    heads = [(zero, zero, one), (one, one, one)]
    for r, s in RAYS:
        x = subtract(one, monomial(s))
        heads.append((x, multiply(monomial(r), x), subtract(monomial(r), monomial(s))))
    for _, _, denominator in heads:
        check_dyadic_unit(denominator)

    occupied = {}
    for i, j in combinations(range(6), 2):
        x, y, h = heads[i]
        u, v, g = heads[j]
        dx = subtract(multiply(x, g), multiply(u, h))
        dy = subtract(multiply(y, g), multiply(v, h))
        check_dyadic_unit(dx)
        exponents = [r for r in range(16) if multiply(monomial(r), dx) == dy]
        check(len(exponents) == 1, "secant must have one certified slope")
        occupied.setdefault(exponents[0], set()).update((i, j))

    # A repeated slope must correspond to one common value on the entire fiber.
    for r, group in occupied.items():
        for i, j in combinations(group, 2):
            x, y, h = heads[i]
            u, v, g = heads[j]
            vi = subtract(y, multiply(x, monomial(r)))
            vj = subtract(v, multiply(u, monomial(r)))
            check(multiply(vi, g) == multiply(vj, h), "disjoint ties on a single fiber")
    memberships = [sum(i in members for members in occupied.values()) for i in range(6)]
    check(memberships == [5, 4, 5, 5, 4, 4], "unexpected fiber counts")
    check(COMMON + FIBER == D, "pair-difference degree")
    free = N - COMMON - len(occupied) * FIBER
    produced = min(COMMON + 4 * FIBER + free // 3, COMMON + 5 * FIBER)
    deficit = sum(max(0, T - COMMON - m * FIBER) for m in memberships)
    check(free - deficit == 1975503 and produced == 380283562, "allocation")
    print(f"Six words at {produced:,} agreements; all fifteen differences have {D:,} shared roots.")


def verify_forced_cliques():
    for count, clique, expected in (
        (N + 1, 4, 410960812476257241),
        (2 * N + 1, 6, 1907347367389145010),
    ):
        low, excess = divmod(count * T, N)
        pairs = comb(count, 2)
        intersections = (N - excess) * comb(low, 2) + excess * comb(low + 1, 2)
        saturated = intersections - (D - 1) * pairs
        check(saturated == expected, "saturated-pair lower bound")
        if count == N + 1:
            neighbors = count * comb(2 * saturated // count, 48) // comb(count, 48)
            check(neighbors == 94, "bipartite saturation")
        check(2 * (clique - 1) * saturated > (clique - 2) * count**2, "Turán inequality")
        print(f"{count:,} words force at least {saturated:,} saturated pairs and a {clique}-clique.")
    residual = (4 * T - N - 3 * D + 2) // 3
    check(residual == 14035080, "minimum residual pencil degree")


if __name__ == "__main__":
    verify_forced_cliques()
    verify_heads()
    cap = 1
    for dimension in range(1, 18):
        common = D + 1 - dimension
        cap = cap * (N - common) // (T - common)
        certified = {1: 3, 2: 11, 15: 413761349, 16: 1584055105, 17: 6064439257}
        if dimension in certified:
            check(cap == certified[dimension], "affine dimension bound")
