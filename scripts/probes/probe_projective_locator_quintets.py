#!/usr/bin/env python3
"""Check the four- and five-site projective locator bounds at order 128; needs python-flint."""

from collections import Counter
from itertools import combinations
from random import Random

from flint import nmod_mat

from probe_projective_locator_information import (
    MODULUS, affine_orbit, affine_orbits, constraint_columns, primitive_exponents,
    require, weight_cap,
)

ORDER = 128


def low_load_certificate(columns, rank):
    """Find injective coordinate projections with maximum relative load at most 2/5."""
    count = len(columns)
    load = [0] * count
    rng = Random(17)
    for samples in range(1, 11):
        indices = list(range(count))
        rng.shuffle(indices)
        indices.sort(key=load.__getitem__, reverse=True)
        matrix = nmod_mat([columns[i] for i in indices], MODULUS).transpose()
        reduced, new_rank = matrix.rref()
        require(new_rank == rank, "column permutation changed the rank")
        basis = []
        previous = -1
        for row in reduced.tolist()[:rank]:
            pivot = next(j for j in range(previous + 1, count) if row[j])
            basis.append(indices[pivot])
            previous = pivot
        require(nmod_mat([columns[i] for i in basis], MODULUS).rank() == rank,
                "information complement is dependent")
        for i in set(range(count)).difference(basis):
            load[i] += 1
        require(sum(load) == samples * (count - rank), "wrong information-set size")
        if 5 * max(load) <= 2 * samples:
            return samples
    raise ArithmeticError("no sufficiently balanced projection family")


def translate_to_zero(anchors):
    return tuple(j - anchors[0] for j in anchors)


def main():
    primitive = primitive_exponents(ORDER)
    large_representatives, large_orbits = [], set()
    quartet_dimensions, sample_counts = Counter(), Counter()
    for anchors, orbit in affine_orbits(ORDER, 4):
        columns = constraint_columns(ORDER, anchors, primitive)
        rank = nmod_mat(columns, MODULUS).rank()
        dimension = len(columns) - rank
        quartet_dimensions[dimension] += 1
        sample_counts[low_load_certificate(columns, rank)] += 1
        if dimension >= 30:
            large_representatives.append(anchors)
            large_orbits.update(orbit)
    require(sum(quartet_dimensions.values()) == 1594 and max(quartet_dimensions) == 46,
            "unexpected quartet nullity census")
    require(len(large_representatives) == 541 and len(large_orbits) == 68415,
            "unexpected number of large quartet orbits")
    print(f"Order 128, 1,594 quartet classes: maximum dimension 46, all projection loads "
          f"at most 2/5, family sizes {dict(sorted(sample_counts.items()))}.")

    seen, quintet_dimensions = set(), Counter()
    for anchors in large_representatives:
        for j in range(ORDER):
            if j in anchors:
                continue
            five = tuple(sorted((*anchors, j)))
            if five in seen:
                continue
            if any(translate_to_zero(four) not in large_orbits
                   for four in combinations(five, 4)):
                continue
            orbit = affine_orbit(ORDER, five)
            require(orbit.isdisjoint(seen), "quintet orbits overlap")
            seen.update(orbit)
            columns = constraint_columns(ORDER, five, primitive)
            dimension = len(columns) - nmod_mat(columns, MODULUS).rank()
            quintet_dimensions[dimension] += 1
    require(quintet_dimensions == {26: 3323, 27: 712, 28: 42, 29: 8},
            "unexpected five-pole residual census")
    print(f"All five-site sets containing only quartets of dimension at least 30: "
          f"{dict(sorted(quintet_dimensions.items()))}; every dimension is at most 29.")

    for size, expected in [(11, 328_065), (19, 192_764_400)]:
        cap = weight_cap(46, ORDER - 4, size, samples=5, maximum_load=2)
        require(cap == expected, "quartet weight cap mismatch")
        print(f"Order 128, four poles, support size {size}: at most {cap:,} locators.")


if __name__ == "__main__":
    main()
