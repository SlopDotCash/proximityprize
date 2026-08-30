#!/usr/bin/env python3
# Copyright (c) 2026 geofflava. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: geofflava
"""Exact F_41[u]/(u^2-3) diagnostic for the CLM-046 fingerprint route.

This standalone, stdlib-only probe reconstructs the five-core certificate
used as a finite diagnostic for the reviewed human proof. It is not the
all-parameter proof and supplies no registered claim or obligation evidence.

All arithmetic is exact. Every advertised value is protected by a hard
assertion; a successful run prints the certificate and exits with status 0.
"""

from collections import Counter
from itertools import combinations

PRIME = 41
NONRESIDUE = 3
FIELD_ORDER = PRIME * PRIME
CORE_SIZE = 8

B_PAIRS = (
    (9, 1),
    (34, 2),
    (17, 3),
    (8, 4),
    (3, 5),
    (40, 6),
    (36, 7),
    (13, 8),
    (30, 9),
    (3, 10),
)
CORE_REPRESENTATIVES = (1, 10, 16, 18, 37)
EXPECTED_CORE_SHIFTS = (1, 16, 37, 10, 18)
EXPECTED_EXTRAS = (41, 42, 43, 44, 45, 46, 48)
EXPECTED_FIRST_SUPPORT_RATIOS = (306, 128, 274, 256, 156)


def field_encode(real, u_coefficient):
    """Encode real + u_coefficient*u as real + 41*u_coefficient."""

    assert isinstance(real, int) and not isinstance(real, bool)
    assert isinstance(u_coefficient, int) and not isinstance(u_coefficient, bool)
    assert 0 <= real < PRIME and 0 <= u_coefficient < PRIME
    return real + PRIME * u_coefficient


def field_decode(value):
    """Decode one canonical integer representative of the extension field."""

    assert isinstance(value, int) and not isinstance(value, bool)
    assert 0 <= value < FIELD_ORDER
    return value % PRIME, value // PRIME


def field_add(left, right):
    """Add two encoded field elements."""

    left_real, left_u = field_decode(left)
    right_real, right_u = field_decode(right)
    return field_encode(
        (left_real + right_real) % PRIME,
        (left_u + right_u) % PRIME,
    )


def field_negate(value):
    """Return the additive inverse of one encoded field element."""

    real, u_coefficient = field_decode(value)
    return field_encode((-real) % PRIME, (-u_coefficient) % PRIME)


def field_subtract(left, right):
    """Subtract two encoded field elements."""

    return field_add(left, field_negate(right))


def field_multiply(left, right):
    """Multiply exactly in F_41[u]/(u^2-3)."""

    left_real, left_u = field_decode(left)
    right_real, right_u = field_decode(right)
    return field_encode(
        (left_real * right_real + NONRESIDUE * left_u * right_u) % PRIME,
        (left_real * right_u + left_u * right_real) % PRIME,
    )


def field_power(base, exponent):
    """Raise an encoded field element to a nonnegative integer power."""

    field_decode(base)
    assert isinstance(exponent, int) and not isinstance(exponent, bool)
    assert exponent >= 0
    result = 1
    factor = base
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = field_multiply(result, factor)
        factor = field_multiply(factor, factor)
        remaining >>= 1
    return result


def field_divide(numerator, denominator):
    """Divide exactly, rejecting a zero denominator."""

    field_decode(numerator)
    field_decode(denominator)
    assert denominator != 0
    inverse = field_power(denominator, FIELD_ORDER - 2)
    assert field_multiply(denominator, inverse) == 1
    return field_multiply(numerator, inverse)


def canonical_fiber_prefix(points, expected_label, size=CORE_SIZE):
    """Validate a constant-label fiber and return its least point indices."""

    field_decode(expected_label)
    assert isinstance(size, int) and not isinstance(size, bool) and size > 0
    exact_points = tuple(points)
    assert len(exact_points) >= size
    indices = []
    for point, label in exact_points:
        field_decode(point)
        field_decode(label)
        assert label == expected_label
        indices.append(point)
    assert len(indices) == len(set(indices))
    return tuple(sorted(indices)[:size])


def main():
    """Reconstruct and check every advertised exact diagnostic value."""

    assert pow(NONRESIDUE, (PRIME - 1) // 2, PRIME) == PRIME - 1
    elements = tuple(
        field_encode(real, u_coefficient)
        for u_coefficient in range(PRIME)
        for real in range(PRIME)
    )
    assert elements == tuple(range(FIELD_ORDER))
    for value in elements:
        assert field_encode(*field_decode(value)) == value
        assert field_power(value, FIELD_ORDER) == value
        if value:
            assert field_multiply(value, field_power(value, FIELD_ORDER - 2)) == 1

    b_values = tuple(field_encode(*pair) for pair in B_PAIRS)
    eighth_powers = tuple(field_power(value, CORE_SIZE) for value in elements)
    blocks = tuple(
        tuple(value for value, power in zip(elements, eighth_powers, strict=True)
              if power == b_value)
        for b_value in b_values
    )
    assert tuple(len(block) for block in blocks) == (CORE_SIZE,) * 10
    root_union = tuple(sorted(point for block in blocks for point in block))
    assert len(root_union) == 80 and len(set(root_union)) == 80

    base_field = set(range(PRIME))
    root_set = set(root_union)
    extras = tuple(
        value
        for value in elements
        if value not in base_field and value not in root_set
    )[:7]
    assert extras == EXPECTED_EXTRAS
    outside_points = root_union + extras
    assert len(outside_points) == 87 and len(set(outside_points)) == 87

    roots_of_unity = tuple(
        value for value in range(1, PRIME) if pow(value, CORE_SIZE, PRIME) == 1
    )
    assert roots_of_unity == (1, 3, 9, 14, 27, 32, 38, 40)
    cores = tuple(
        tuple(sorted(representative * root % PRIME for root in roots_of_unity))
        for representative in CORE_REPRESENTATIVES
    )
    shifts = tuple(pow(representative, CORE_SIZE, PRIME)
                   for representative in CORE_REPRESENTATIVES)
    assert shifts == EXPECTED_CORE_SHIFTS
    assert all(len(core) == CORE_SIZE and len(set(core)) == CORE_SIZE for core in cores)

    challenge_labels = tuple(
        tuple(field_subtract(b_value, shift) for b_value in b_values)
        for shift in shifts
    )
    reciprocal_labels = tuple(
        tuple(field_subtract(shift, b_value) for b_value in b_values)
        for shift in shifts
    )
    flat_challenges = tuple(label for row in challenge_labels for label in row)
    flat_reciprocals = tuple(label for row in reciprocal_labels for label in row)
    assert len(flat_challenges) == len(set(flat_challenges)) == 50
    assert len(flat_reciprocals) == len(set(flat_reciprocals)) == 50
    assert 0 not in flat_challenges and 0 not in flat_reciprocals
    assert all(
        field_add(challenge, reciprocal) == 0
        for challenge, reciprocal in zip(flat_challenges, flat_reciprocals, strict=True)
    )

    for shift, label_row in zip(shifts, reciprocal_labels, strict=True):
        for block, expected_label in zip(blocks, label_row, strict=True):
            full_fiber = tuple(
                (point, field_subtract(shift, field_power(point, CORE_SIZE)))
                for point in outside_points
                if field_subtract(shift, field_power(point, CORE_SIZE))
                == expected_label
            )
            assert canonical_fiber_prefix(full_fiber, expected_label) == block

    canonical_block_indices = tuple(sorted(range(10), key=blocks.__getitem__))
    inputs = []
    for core_index in range(len(cores)):
        for first_index, second_index in combinations(canonical_block_indices, 2):
            ordered_blocks = (blocks[first_index], blocks[second_index])
            ordered_labels = (
                reciprocal_labels[core_index][first_index],
                reciprocal_labels[core_index][second_index],
            )
            ratio = field_divide(ordered_labels[0], ordered_labels[1])
            assert field_multiply(ratio, ordered_labels[1]) == ordered_labels[0]
            inputs.append((core_index, ordered_blocks, ordered_labels, ratio))

    plain_buckets = Counter(entry[1] for entry in inputs)
    enriched_fingerprints = {(*entry[1], entry[3]) for entry in inputs}
    assert len(inputs) == 225
    assert len(plain_buckets) == 45
    assert tuple(sorted(plain_buckets.values())) == (5,) * 45
    assert len(enriched_fingerprints) == 225

    first_support = min(plain_buckets)
    first_support_ratios = tuple(
        entry[3] for entry in inputs if entry[1] == first_support
    )
    assert first_support_ratios == EXPECTED_FIRST_SUPPORT_RATIOS

    print("CLM-046 F41 two-label reciprocal-fingerprint diagnostic")
    print(f"field elements: {len(elements)}; outside points: {len(outside_points)}")
    print(f"core representatives: {CORE_REPRESENTATIVES}; shifts: {shifts}")
    print("selected labels: 50 challenge and 50 reciprocal, all distinct and nonzero")
    print("sign convention: delta=b-s; a=s-b=-delta")
    print(
        "fingerprints: "
        f"inputs={len(inputs)}, plain buckets={len(plain_buckets)}, "
        f"plain multiplicities={set(plain_buckets.values())}, "
        f"enriched={len(enriched_fingerprints)}"
    )
    print(f"first support ratios: {first_support_ratios}")
    print("PASS: all exact assertions reproduced")


if __name__ == "__main__":
    main()
