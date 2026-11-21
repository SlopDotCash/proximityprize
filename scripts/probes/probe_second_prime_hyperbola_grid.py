#!/usr/bin/env python3
"""Check the six hyperbola heads, their nine equality fibers and the half-rate count."""

from itertools import combinations
from math import comb

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import GENERATOR, PRIME


def main():
    length = 2**30
    scale = length // 16
    root = pow(GENERATOR, scale, PRIME)
    require(pow(root, 8, PRIME) == PRIME - 1, "order of the power quotient")
    vertical = [pow(root, i, PRIME) for i in (0, 1, 2)]
    horizontal = [pow(root, i, PRIME) for i in (0, 3, 6)]
    core_sizes = [0] * 6
    labels = 0
    common = 0
    for j in range(16):
        t = pow(root, j, PRIME)
        points = [(a, t * pow(a, -1, PRIME) % PRIME) for a in vertical]
        points += [(t * pow(b, -1, PRIME) % PRIME, b) for b in horizontal]
        collisions = {(i, h) for i, h in combinations(range(6), 2) if points[i] == points[h]}
        expected = {(j % 3, 3 + j // 3)} if j < 9 else set()
        require(collisions == expected, "agreement between the two rulings")
        distinct = set(points)
        require(len({y for _, y in distinct}) == len(distinct), "nonzero denominators")
        for (x, y), (u, v), (z, w) in combinations(distinct, 3):
            require(((u - x) * (w - y) - (z - x) * (v - y)) % PRIME != 0,
                    "distinct foreign directions")
        owner = j % 3 if j < 9 else 0
        roots = 0 if j < 9 else (scale - 2 if j == 15 else scale)
        common += roots
        for i, p in enumerate(points):
            core_sizes[i] += scale if p == points[owner] else roots
            if p != points[owner]:
                labels += scale - roots
    k = length // 2
    errors = length - min(core_sizes) - 1
    require(common + scale + 1 < k <= min(core_sizes), "polynomial degrees and unique fit")
    require(labels == sum(length - c for c in core_sizes), "independent label count")
    require(labels > PRIME // 2**128 and comb(labels, 2) < PRIME, "security and avoidance")
    require((errors, labels) == (402653185, 2415919114), "production ceiling")
    print(f"{errors} errors, {labels} bad scalars, {common} locator roots, core sizes {core_sizes}")


if __name__ == "__main__":
    main()
