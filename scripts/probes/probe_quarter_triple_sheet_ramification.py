#!/usr/bin/env python3
"""Verify the ordered-triple ramification arithmetic and finite permutation checks."""

from fractions import Fraction as Q
from itertools import permutations
from math import lcm


N = 2**30
D = N // 4 - 2
P = 365375409332725729550921208179070755120141565953
FLOOR = Q(45663621513021794134939, 103042957874781541548323)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def falling_three(fixed):
    return fixed * (fixed - 1) * (fixed - 2)


def tangent(b):
    return 3 * b * (b - 1), 2 * b * (b - 1) * (b + 1)


def partitions(total, minimum=1):
    if not total:
        yield ()
        return
    for first in range(minimum, total + 1):
        for rest in partitions(total - first, first):
            yield (first, *rest)


def representative(lengths):
    mapping = []
    first = 0
    for length in lengths:
        mapping.extend(range(first + 1, first + length))
        mapping.append(first)
        first += length
    return mapping


def direct_orbit_count(mapping, arity):
    remaining = set(permutations(range(len(mapping)), arity))
    count = 0
    while remaining:
        item = next(iter(remaining))
        count += 1
        while item in remaining:
            remaining.remove(item)
            item = tuple(mapping[i] for i in item)
    return count


def check_permutations():
    classes = 0
    for m in range(3, 10):
        for cycle_type in partitions(m):
            classes += 1
            mapping = representative(cycle_type)
            order = lcm(*cycle_type)
            for arity, degree in [(1, m), (3, falling_three(m))]:
                direct = direct_orbit_count(mapping, arity)
                # Repeating all powers also tests the nominal-order step of the proof.
                for nominal in [order, 2 * order]:
                    total_index = 0
                    power = list(range(m))
                    for _ in range(1, nominal):
                        power = [mapping[i] for i in power]
                        fixed = sum(i == image for i, image in enumerate(power))
                        fixed_tuples = fixed if arity == 1 else falling_three(fixed)
                        total_index += degree - fixed_tuples
                    require(total_index == nominal * (degree - direct), (cycle_type, arity))
    require(classes == 93, classes)
    return classes


def check_stage(m, h, b, expected):
    a = (m - 1) * (m - 2)
    lower_genus = a * (Q(3 * m, 7) - 6 - Q(8, 7 * h))
    slope, intercept = tangent(b)
    coefficient = m * a - m * slope + intercept
    require(coefficient > 0, coefficient)
    result = (lower_genus + 2 * slope - 2 * intercept) / coefficient
    require(result == expected, result)
    require(b == (m * result + 2) // (result + 2), b)
    require(3 * N * h**3 * a // h < P, "characteristic budget")
    return result


def check_inertia_support():
    # Each rational is the asserted strict upper fraction of fixed sheets.
    for fixed_fraction, order, moved in [
        (Q(82983, 100000), 0, 45679662),
        (Q(13069, 25000), 2, 128108138),
        (Q(1419, 2000), 3, 77980500),
    ]:
        for s, h, m in [(1, 1, D), (1, 2, D // 2), (2, 1, D // 2)]:
            a = (m - 1) * (m - 2)
            # theta=1 gives the upper bound uniform over all orders.
            theta = Q(order - 1, order) if order else Q(1)
            third_cap = a * (m - (Q(3 * m, 7) - (6 + Q(8, 7 * h)) / s) / theta)
            b = (fixed_fraction * m).__floor__()
            slope, intercept = tangent(b)
            require(slope * fixed_fraction * m - intercept > third_cap, (s, h, m, order))
        minimum_moved = D - ((fixed_fraction * D).__ceil__() - 1)
        if order > 1:
            minimum_moved = -(-minimum_moved // order) * order
        require(minimum_moved == moved, (minimum_moved, moved))


def main():
    for fixed in range(101):
        for b in range(1, 101):
            slope, intercept = tangent(b)
            require(falling_three(fixed) >= slope * fixed - intercept, (fixed, b))
    print(f"Verified all {check_permutations()} cycle types of degrees 3 through 9.")
    for m, h, b, expected in [
        (D // 2, 2, 24345100, FLOOR),
        (D, 1, 48690201, Q(9243648649097604732874, 20858898488376704579481)),
    ]:
        print(f"Outer degree one, inner degree {h}, excess >= {check_stage(m, h, b, expected)}.")
    require(Q(268435426, 2 * 268435465) > FLOOR > Q(4431513, 10**7), "whole floor")
    for first, second in [(2, 17), (3, 4)]:
        require(1 - Q(1, first) - Q(1, second) < FLOOR, (first, second))
    for first, second, least in [(2, 18, 774), (2, 19, 238), (3, 5, 43), (4, 4, 18)]:
        limit = 1 - Q(1, first) - Q(1, second) - FLOOR
        require((1 / limit).__ceil__() == least, (first, second, least))
    check_inertia_support()
    for m in (D, D // 2):
        a = (m - 1) * (m - 2)
        excess = m - 3
        genus_term = m * a * excess - (m - 1) * falling_three(m - 2)
        require(genus_term == 4 * a * (m - 3), genus_term)
        require(genus_term / Q(a) > Q(6 * m, 7), "transposition example")
    print("Verified moved-sheet floors 45679662, 128108138, and 77980500.")


if __name__ == "__main__":
    main()
