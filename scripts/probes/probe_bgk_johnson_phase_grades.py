#!/usr/bin/env python3
"""Exact Johnson-grade decomposition of the primitive-14th-root seven-subset phase vector.

All arithmetic before the final Vandermonde solve is in the integral group ring Z[C_14].
Evaluation at a primitive fourteenth root uses

    zeta^7 = -1,
    Phi_14(zeta) = zeta^6-zeta^5+zeta^4-zeta^3+zeta^2-zeta+1 = 0.

No floating point or external package is used.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


N_PHASES = 14
DEPTH = 7


def reduce_at_primitive_14(coefficients: list[int]) -> tuple[int, ...]:
    """Reduce a Z[C_14] element to the basis 1,zeta,...,zeta^5."""
    assert len(coefficients) == 14
    degree_six = [coefficients[i] - coefficients[i + 7] for i in range(7)]
    top = degree_six[6]
    return (
        degree_six[0] - top,
        degree_six[1] + top,
        degree_six[2] - top,
        degree_six[3] + top,
        degree_six[4] - top,
        degree_six[5] + top,
    )


def phase_power_sum(power: int) -> tuple[int, ...]:
    coefficients = [0] * N_PHASES
    for exponent in range(N_PHASES):
        coefficients[(power * exponent) % N_PHASES] += 1
    return reduce_at_primitive_14(coefficients)


def solve_vandermonde(eigenvalues: list[int], moments: list[int]) -> list[Fraction]:
    size = len(eigenvalues)
    matrix = [
        [Fraction(eigenvalues[i] ** power) for i in range(size)]
        + [Fraction(moments[power])]
        for power in range(size)
    ]
    for column in range(size):
        pivot = next(row for row in range(column, size) if matrix[row][column])
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        scale = matrix[column][column]
        matrix[column] = [entry / scale for entry in matrix[column]]
        for row in range(size):
            if row == column:
                continue
            factor = matrix[row][column]
            if factor:
                matrix[row] = [
                    matrix[row][j] - factor * matrix[column][j]
                    for j in range(size + 1)
                ]
    return [matrix[i][-1] for i in range(size)]


def format_fraction(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def exact_moments() -> tuple[list[int], list[int]]:
    subsets = list(combinations(range(N_PHASES), DEPTH))
    index = {subset: position for position, subset in enumerate(subsets)}
    neighbors: list[list[int]] = []
    for subset in subsets:
        support = set(subset)
        row: list[int] = []
        for removed in subset:
            for added in range(N_PHASES):
                if added not in support:
                    neighbor = tuple(sorted((support - {removed}) | {added}))
                    row.append(index[neighbor])
        neighbors.append(row)

    phase_exponents = [sum(subset) % N_PHASES for subset in subsets]
    vector = [[0] * N_PHASES for _ in subsets]
    for position, exponent in enumerate(phase_exponents):
        vector[position][exponent] = 1

    moments: list[int] = []
    for power in range(DEPTH + 1):
        inner_group_ring = [0] * N_PHASES
        for position, phase_exponent in enumerate(phase_exponents):
            for exponent, coefficient in enumerate(vector[position]):
                inner_group_ring[(exponent - phase_exponent) % N_PHASES] += coefficient
        reduced = reduce_at_primitive_14(inner_group_ring)
        assert reduced[1:] == (0, 0, 0, 0, 0)
        moments.append(reduced[0])

        if power < DEPTH:
            next_vector = [[0] * N_PHASES for _ in subsets]
            for position, row in enumerate(neighbors):
                target = next_vector[position]
                for neighbor in row:
                    source = vector[neighbor]
                    for exponent in range(N_PHASES):
                        target[exponent] += source[exponent]
            vector = next_vector
    return moments, [len(subsets), len(neighbors[0])]


def main() -> None:
    assert all(phase_power_sum(power) == (0, 0, 0, 0, 0, 0) for power in range(1, 8))
    moments, (vertices, degree) = exact_moments()
    eigenvalues = [49, 35, 23, 13, 5, -1, -5, -7]
    masses = solve_vandermonde(eigenvalues, moments)
    expected = [
        Fraction(0),
        Fraction(1, 66),
        Fraction(7, 6),
        Fraction(273, 11),
        Fraction(637, 3),
        Fraction(5005, 6),
        Fraction(3003, 2),
        Fraction(858),
    ]
    assert masses == expected
    assert sum(masses) == vertices
    assert sum(masses[1:7]) == 3 * masses[7]
    assert 16 * masses[6] == 7 * vertices

    print("JOHNSON_PHASE_GRADE_EXACT")
    print(f"n=14 k=7 vertices={vertices} degree={degree}")
    print("power_sums_1_through_7=0")
    print(f"eigenvalues={eigenvalues}")
    print(f"adjacency_moments={moments}")
    print("grade_masses=[" + ", ".join(format_fraction(value) for value in masses) + "]")
    print("lower_grades_1_through_6=2574 top_grade_7=858 ratio=3")
    print("largest_grade=6 mass=3003/2 share=7/16")
    print(
        "VERDICT=REFUTED: vanishing Newton power sums through depth seven do not remove "
        "Johnson grades 1..6; grade 6 is load-bearing"
    )


if __name__ == "__main__":
    main()
