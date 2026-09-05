#!/usr/bin/env python3
# Copyright (c) 2026 geofflava. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: geofflava
"""Exact F7 diagnostic for the CLM-045 reciprocal-pencil route.

This standalone, stdlib-only probe exhausts the finite ``F_7`` model and
recomputes the colored-moment arithmetic. It is a scaled route diagnostic,
not an E87 instance and not evidence for the accompanying human proof.

All arithmetic is exact. Every advertised value is protected by a hard
assertion; a successful run prints the certificate and exits with status 0.
"""

from collections import Counter
from itertools import product
from math import comb, prod

PRIME = 7
LABELS = tuple(range(PRIME))
INSIDE_POINTS = (0, 1, 2, 3, 4)
OUTSIDE_POINTS = (5, 6)
FUNCTION_VALUES = (0, 0, 0, 1, 5, 1, 3)

EXPECTED_HISTOGRAM = {0: 16, 1: 22, 2: 6, 3: 5}
EXPECTED_OUTSIDE_SUPPORT = (1, 3)
EXPECTED_LAMBDA_ROW = (5, 5, 3)
EXPECTED_K_ROWS = ((1, 0, 2), (0, 5, 0))
EXPECTED_L_ROWS = ((0, 5, 2), (3, 6, 3))
EXPECTED_KERNELS = (
    (2, 3, 1),
    (5, 0, 1),
    (3, 2, 1),
    (6, 6, 1),
    (1, 4, 1),
    (6, 1, 0),
    (0, 5, 1),
)
EXPECTED_ROOT_SETS = ((), (3, 4), (), (), (), (1,), (0, 2))

PASSING_CORE_CAP = 2_729_892
PER_CORE_LABEL_CAP = 10
TARGET_MASS = 19_731_940
EXPECTED_BASE = 7
EXPECTED_REMAINDER = 622_696
EXPECTED_PAIR_MASS_AT_TARGET = 61_686_604
EXPECTED_PAIR_MASS_ABOVE_TARGET = 61_686_611
EXPECTED_SUFFICIENT_CAP = 61_686_610


def inverse(value):
    """Return the multiplicative inverse of a nonzero residue in F7."""

    residue = value % PRIME
    assert residue != 0
    result = pow(residue, PRIME - 2, PRIME)
    assert residue * result % PRIME == 1
    return result


def polynomial_value(coefficients, point):
    """Evaluate a low-degree coefficient tuple in F7 by Horner's rule."""

    result = 0
    for coefficient in reversed(coefficients):
        result = (result * point + coefficient) % PRIME
    return result


def agreement_histogram():
    """Exhaust all 49 affine words and count agreements with the fixture."""

    histogram = Counter()
    for intercept, slope in product(range(PRIME), repeat=2):
        agreements = sum(
            value == (intercept + slope * point) % PRIME
            for point, value in enumerate(FUNCTION_VALUES)
        )
        histogram[agreements] += 1
    return dict(sorted(histogram.items()))


def interpolation_rows():
    """Recompute Lambda and the two reciprocal interpolation rows."""

    alphas = tuple(
        inverse(
            prod(
                (point - other) % PRIME
                for other in INSIDE_POINTS
                if other != point
            )
        )
        for point in INSIDE_POINTS
    )
    lambda_row = tuple(
        sum(
            alpha * FUNCTION_VALUES[point] * pow(point, exponent, PRIME)
            for point, alpha in zip(INSIDE_POINTS, alphas, strict=True)
        )
        % PRIME
        for exponent in range(3)
    )
    k_rows = tuple(
        tuple(
            prod((outside - point) % PRIME for point in INSIDE_POINTS)
            * sum(
                alpha
                * FUNCTION_VALUES[point]
                * pow(point, exponent, PRIME)
                * inverse(outside - point)
                for point, alpha in zip(INSIDE_POINTS, alphas, strict=True)
            )
            % PRIME
            for exponent in range(3)
        )
        for outside in OUTSIDE_POINTS
    )
    return lambda_row, k_rows


def evaluation_row(point):
    """Return the coefficient-basis evaluation row at one F7 point."""

    return (1, point, point * point % PRIME)


def dot(row, vector):
    """Compute an exact F7 row-vector product."""

    return sum(
        coefficient * value
        for coefficient, value in zip(row, vector, strict=True)
    ) % PRIME


def determinant(rows):
    """Compute a 3-by-3 determinant in F7."""

    return (
        rows[0][0] * (rows[1][1] * rows[2][2] - rows[1][2] * rows[2][1])
        - rows[0][1] * (rows[1][0] * rows[2][2] - rows[1][2] * rows[2][0])
        + rows[0][2] * (rows[1][0] * rows[2][1] - rows[1][1] * rows[2][0])
    ) % PRIME


def trim_polynomial(coefficients):
    """Normalize a coefficient list as a polynomial over F7."""

    result = [coefficient % PRIME for coefficient in coefficients]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def polynomial_add(left, right):
    """Add two coefficient tuples over F7."""

    length = max(len(left), len(right))
    return trim_polynomial(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(length)
    )


def polynomial_negate(coefficients):
    """Negate a coefficient tuple over F7."""

    return trim_polynomial(-coefficient for coefficient in coefficients)


def polynomial_subtract(left, right):
    """Subtract two coefficient tuples over F7."""

    return polynomial_add(left, polynomial_negate(right))


def polynomial_multiply(left, right):
    """Multiply two coefficient tuples over F7."""

    result = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return trim_polynomial(result)


def determinant_polynomial(lambda_row, l_rows, v_rows):
    """Compute det(Lambda; a L_5 - V_5; a L_6 - V_6) in F7[a]."""

    matrix = (
        tuple((coefficient,) for coefficient in lambda_row),
        tuple(
            (-v_value % PRIME, l_value)
            for l_value, v_value in zip(l_rows[0], v_rows[0], strict=True)
        ),
        tuple(
            (-v_value % PRIME, l_value)
            for l_value, v_value in zip(l_rows[1], v_rows[1], strict=True)
        ),
    )
    first_minor = polynomial_subtract(
        polynomial_multiply(matrix[1][1], matrix[2][2]),
        polynomial_multiply(matrix[1][2], matrix[2][1]),
    )
    second_minor = polynomial_subtract(
        polynomial_multiply(matrix[1][0], matrix[2][2]),
        polynomial_multiply(matrix[1][2], matrix[2][0]),
    )
    third_minor = polynomial_subtract(
        polynomial_multiply(matrix[1][0], matrix[2][1]),
        polynomial_multiply(matrix[1][1], matrix[2][0]),
    )
    result = polynomial_add(
        polynomial_subtract(
            polynomial_multiply(matrix[0][0], first_minor),
            polynomial_multiply(matrix[0][1], second_minor),
        ),
        polynomial_multiply(matrix[0][2], third_minor),
    )
    return result + (0,) * (3 - len(result))


def pencil_matrix(label, lambda_row, l_rows, v_rows):
    """Build the reciprocal-pencil matrix at one label."""

    return (
        lambda_row,
        *(
            tuple(
                (label * l_value - v_value) % PRIME
                for l_value, v_value in zip(l_row, v_row, strict=True)
            )
            for l_row, v_row in zip(l_rows, v_rows, strict=True)
        ),
    )


def normalized_kernel(rows):
    """Exhaust all 343 vectors and return the unique projective kernel."""

    normalized = set()
    for vector in product(range(PRIME), repeat=3):
        if vector == (0, 0, 0) or any(dot(row, vector) for row in rows):
            continue
        leading_index = max(
            index for index, coefficient in enumerate(vector) if coefficient
        )
        leading_inverse = inverse(vector[leading_index])
        normalized.add(
            tuple(coefficient * leading_inverse % PRIME for coefficient in vector)
        )
    assert len(normalized) == 1
    return normalized.pop()


def minimum_pair_mass(total, core_cap, label_cap):
    """Minimize sum_A binom(m_A, 2) under exact integer caps."""

    assert 0 <= total <= core_cap * label_cap
    base, remainder = divmod(total, core_cap)
    assert base <= label_cap
    return (
        (core_cap - remainder) * comb(base, 2)
        + remainder * comb(base + 1, 2)
    )


def main():
    """Recompute every diagnostic and threshold value, then print them."""

    histogram = agreement_histogram()
    assert histogram == EXPECTED_HISTOGRAM
    assert sum(histogram.values()) == PRIME * PRIME
    assert max(histogram) == 3

    lambda_row, k_rows = interpolation_rows()
    outside_support = tuple(FUNCTION_VALUES[point] for point in OUTSIDE_POINTS)
    evaluation_rows = tuple(evaluation_row(point) for point in OUTSIDE_POINTS)
    l_rows = tuple(
        tuple(
            (support * evaluation_value - k_value) % PRIME
            for evaluation_value, k_value in zip(
                evaluation_row_values, k_row, strict=True
            )
        )
        for support, evaluation_row_values, k_row in zip(
            outside_support, evaluation_rows, k_rows, strict=True
        )
    )
    v_rows = tuple(
        tuple(support * value % PRIME for value in evaluation_row_values)
        for support, evaluation_row_values in zip(
            outside_support, evaluation_rows, strict=True
        )
    )

    assert FUNCTION_VALUES == (0, 0, 0, 1, 5, 1, 3)
    assert INSIDE_POINTS == (0, 1, 2, 3, 4)
    assert OUTSIDE_POINTS == (5, 6)
    assert outside_support == EXPECTED_OUTSIDE_SUPPORT
    assert lambda_row == EXPECTED_LAMBDA_ROW
    assert k_rows == EXPECTED_K_ROWS
    assert l_rows == EXPECTED_L_ROWS

    determinant_coefficients = determinant_polynomial(
        lambda_row, l_rows, v_rows
    )
    assert determinant_coefficients == (0, 0, 0)

    matrices = tuple(
        pencil_matrix(label, lambda_row, l_rows, v_rows) for label in LABELS
    )
    determinants = tuple(determinant(matrix) for matrix in matrices)
    kernels = tuple(normalized_kernel(matrix) for matrix in matrices)
    root_sets = tuple(
        tuple(
            point
            for point in INSIDE_POINTS
            if polynomial_value(kernel, point) == 0
        )
        for kernel in kernels
    )

    assert determinants == (0,) * PRIME
    assert kernels == EXPECTED_KERNELS
    assert root_sets == EXPECTED_ROOT_SETS
    for label, matrix, kernel in zip(LABELS, matrices, kernels, strict=True):
        assert determinant(matrix) == 0, label
        assert all(dot(row, kernel) == 0 for row in matrix), label
        leading_index = max(
            index for index, coefficient in enumerate(kernel) if coefficient
        )
        assert kernel[leading_index] == 1, label

    base, remainder = divmod(TARGET_MASS, PASSING_CORE_CAP)
    pair_mass_at_target = minimum_pair_mass(
        TARGET_MASS, PASSING_CORE_CAP, PER_CORE_LABEL_CAP
    )
    pair_mass_above_target = minimum_pair_mass(
        TARGET_MASS + 1, PASSING_CORE_CAP, PER_CORE_LABEL_CAP
    )
    sufficient_cap = pair_mass_above_target - 1

    assert base == EXPECTED_BASE
    assert remainder == EXPECTED_REMAINDER
    assert TARGET_MASS == 7 * PASSING_CORE_CAP + 622_696
    assert pair_mass_at_target == EXPECTED_PAIR_MASS_AT_TARGET
    assert pair_mass_above_target == EXPECTED_PAIR_MASS_ABOVE_TARGET
    assert sufficient_cap == EXPECTED_SUFFICIENT_CAP
    assert pair_mass_at_target == 21 * PASSING_CORE_CAP + 7 * 622_696
    assert pair_mass_above_target == 21 * PASSING_CORE_CAP + 7 * 622_697

    print("CLM-045 F7 reciprocal-pencil diagnostic")
    print(f"agreement histogram: {histogram}")
    print(f"Lambda: {lambda_row}; K rows: {k_rows}; L rows: {l_rows}")
    print(f"determinant polynomial: {determinant_coefficients}")
    print(f"determinants by label: {determinants}")
    print(f"normalized kernels: {kernels}")
    print(f"inside-root sets: {root_sets}")
    print(
        "colored moment: "
        f"P={PASSING_CORE_CAP}, cap={PER_CORE_LABEL_CAP}, "
        f"T={TARGET_MASS}, Q(T)={pair_mass_at_target}, "
        f"Q(T+1)={pair_mass_above_target}, sufficient cap={sufficient_cap}"
    )
    print("PASS: all exact assertions reproduced")


if __name__ == "__main__":
    main()
