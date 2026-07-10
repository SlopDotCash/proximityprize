#!/usr/bin/env python3
"""Probe scalar-label sensitivity of the P1 abstract-incidence rank test.

The support masks and order-64 evaluation domains come from
``probe_rate_quarter_p1_abstract_incidence_rank.py``.  For each of F_193,
F_257, and F_449 this script tests a reproducible menu of distinct scalar
labellings:

* support-independent algebraic sets (powers, a geometric progression, and
  ``{0} union mu_64``);
* support-correlated permutations and two matching-based adversarial
  assignments;
* deterministic pseudorandom permutations, injections, and subgroup
  permutations.

Ranks are exact.  A fixed nonsingular 1008-row minor from the consecutive
labelling certifies most cases; if that minor is singular, the script falls
back to eliminating the full 2212-by-1008 matrix.

The last section is exhaustive rather than sampled.  Holding 64 consecutive
labels fixed, it replaces each of gamma_60,...,gamma_64 by every field value
that remains distinct.  A row-update determinant lemma checks the same fixed
minor for all values and full elimination handles any exceptional value.

This is evidence about one fixed support family over three small fields.  A
full-rank specialization proves generic full rank for this polynomial matrix
family in each tested characteristic, but neither the finite sweep nor that
genericity statement proves full rank for every distinct labelling.

Requires NumPy.  Deterministic; expected runtime is roughly two minutes.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Callable, Sequence

import numpy as np

import probe_rate_quarter_p1_abstract_incidence_rank as base


PRIMES = (193, 257, 449)
MASTER_SEED = 0x466A11CE5EED2026
RANDOM_PERMUTATIONS = 8
RANDOM_INJECTIONS = 8
RANDOM_SUBGROUP_PERMUTATIONS = 4
TAIL_EVENTS = tuple(range(60, 65))
EXPECTED_COLUMNS = (base.M - 2) * base.K


class SplitMix64:
    """Tiny fully specified PRNG, used only for reproducible probe cases."""

    _MASK = (1 << 64) - 1

    def __init__(self, seed: int) -> None:
        self.state = seed & self._MASK

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & self._MASK
        value = self.state
        value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & self._MASK
        value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & self._MASK
        return (value ^ (value >> 31)) & self._MASK

    def randbelow(self, bound: int) -> int:
        assert bound > 0
        limit = (1 << 64) - ((1 << 64) % bound)
        while True:
            value = self.next_u64()
            if value < limit:
                return value % bound

    def shuffle(self, values: list[int]) -> None:
        for upper in range(len(values) - 1, 0, -1):
            selected = self.randbelow(upper + 1)
            values[upper], values[selected] = values[selected], values[upper]


def order_64_domain(prime: int) -> list[int]:
    generator = base.primitive_root(prime)
    omega = pow(generator, (prime - 1) // base.N, prime)
    domain = [pow(omega, exponent, prime) for exponent in range(base.N)]
    assert len(set(domain)) == base.N
    return domain


def labels_in_event_order(
    values: Sequence[int],
    event_order: Sequence[int],
) -> list[int]:
    assert len(values) == base.M and len(event_order) == base.M
    labels = [0] * base.M
    for value, event in zip(values, event_order, strict=True):
        labels[event] = int(value)
    return labels


def matched_subgroup_labels(
    prime: int,
    predicate: Callable[[int, int], bool],
) -> list[int]:
    """Match all 64 domain elements to events, leaving one event labelled 0."""
    domain = order_64_domain(prime)
    event_to_coordinate = [-1] * base.M

    candidate_events = [
        [event for event in range(base.M) if predicate(event, coordinate)]
        for coordinate in range(base.N)
    ]
    coordinate_order = sorted(
        range(base.N), key=lambda coordinate: len(candidate_events[coordinate])
    )

    def augment(coordinate: int, seen: set[int]) -> bool:
        for event in candidate_events[coordinate]:
            if event in seen:
                continue
            seen.add(event)
            previous = event_to_coordinate[event]
            if previous < 0 or augment(previous, seen):
                event_to_coordinate[event] = coordinate
                return True
        return False

    for coordinate in coordinate_order:
        assert augment(coordinate, set())

    labels = [0] * base.M
    matched_coordinates = set()
    for event, coordinate in enumerate(event_to_coordinate):
        if coordinate >= 0:
            labels[event] = domain[coordinate]
            matched_coordinates.add(coordinate)
    assert len(matched_coordinates) == base.N
    assert len(set(labels)) == base.M
    return labels


def deterministic_cases(prime: int) -> list[tuple[str, str, list[int]]]:
    consecutive = list(range(base.M))
    domain = order_64_domain(prime)
    subgroup = [0, *domain]

    bit_reversal = [
        int(f"{event:06b}"[::-1], 2) if event < base.N else base.N
        for event in range(base.M)
    ]
    mask_order = sorted(range(base.M), key=lambda event: base.MASKS[event])
    hash_order = sorted(
        range(base.M),
        key=lambda event: hashlib.sha256(
            base.MASKS[event].to_bytes(8, "little")
        ).digest(),
    )
    structured_overlap_order = sorted(
        range(base.M),
        key=lambda event: (
            (base.MASKS[event] & base.STRUCTURED_DIRECTION).bit_count(),
            base.MASKS[event],
        ),
    )
    coordinate_moment_order = sorted(
        range(base.M),
        key=lambda event: (
            sum(
                (coordinate + 1) ** 2
                for coordinate in range(base.N)
                if (base.MASKS[event] >> coordinate) & 1
            ),
            base.MASKS[event],
        ),
    )

    generator = base.primitive_root(prime)
    mobius = [
        ((2 * value + 3) * pow(value + 100, prime - 2, prime)) % prime
        for value in consecutive
    ]
    support_match = matched_subgroup_labels(
        prime,
        lambda event, coordinate: bool(
            (base.MASKS[event] >> coordinate) & 1
        ),
    )
    complement_match = matched_subgroup_labels(
        prime,
        lambda event, coordinate: not (
            (base.MASKS[event] >> coordinate) & 1
        ),
    )

    cases = [
        ("consecutive", "baseline", consecutive),
        ("bit_reversal", "support_correlated_permutation", bit_reversal),
        (
            "mask_numeric_order",
            "support_correlated_permutation",
            labels_in_event_order(consecutive, mask_order),
        ),
        (
            "mask_sha256_order",
            "support_correlated_permutation",
            labels_in_event_order(consecutive, hash_order),
        ),
        (
            "structured_overlap_order",
            "support_correlated_permutation",
            labels_in_event_order(consecutive, structured_overlap_order),
        ),
        (
            "coordinate_moment_order",
            "support_correlated_permutation",
            labels_in_event_order(consecutive, coordinate_moment_order),
        ),
        ("squares", "algebraic_label_set", [value * value % prime for value in consecutive]),
        ("fifth_powers", "algebraic_label_set", [pow(value, 5, prime) for value in consecutive]),
        (
            "primitive_geometric_progression",
            "algebraic_label_set",
            [pow(generator, exponent, prime) for exponent in range(base.M)],
        ),
        ("mobius_of_consecutive", "pgl2_metamorphic_check", mobius),
        ("zero_union_mu64", "subgroup_label_set", subgroup),
        (
            "zero_union_mu64_mask_order",
            "support_correlated_subgroup",
            labels_in_event_order(subgroup, mask_order),
        ),
        (
            "zero_union_mu64_support_matching",
            "matching_adversarial",
            support_match,
        ),
        (
            "zero_union_mu64_complement_matching",
            "matching_adversarial",
            complement_match,
        ),
    ]
    for name, _, labels in cases:
        assert len(labels) == base.M, name
        assert len(set(value % prime for value in labels)) == base.M, name
    return cases


def random_cases(prime: int) -> tuple[int, list[tuple[str, str, list[int]]]]:
    field_seed = (MASTER_SEED ^ prime) & ((1 << 64) - 1)
    rng = SplitMix64(field_seed)
    cases = []

    for sample in range(RANDOM_PERMUTATIONS):
        labels = list(range(base.M))
        rng.shuffle(labels)
        cases.append((
            f"random_consecutive_permutation_{sample:02d}",
            "random_consecutive_permutation",
            labels,
        ))

    for sample in range(RANDOM_INJECTIONS):
        population = list(range(prime))
        rng.shuffle(population)
        cases.append((
            f"random_field_injection_{sample:02d}",
            "random_field_injection",
            population[:base.M],
        ))

    subgroup = [0, *order_64_domain(prime)]
    for sample in range(RANDOM_SUBGROUP_PERMUTATIONS):
        labels = subgroup.copy()
        rng.shuffle(labels)
        cases.append((
            f"random_zero_union_mu64_permutation_{sample:02d}",
            "random_subgroup_permutation",
            labels,
        ))

    return field_seed, cases


def independent_row_indices(matrix: np.ndarray, prime: int) -> np.ndarray:
    """Return original indices of the first full set of modular pivot rows."""
    matrix = matrix.copy()
    row_ids = np.arange(matrix.shape[0])
    pivot_row = 0
    for column in range(matrix.shape[1]):
        candidates = np.flatnonzero(matrix[pivot_row:, column])
        if not len(candidates):
            continue
        selected = pivot_row + int(candidates[0])
        matrix[[pivot_row, selected]] = matrix[[selected, pivot_row]]
        row_ids[[pivot_row, selected]] = row_ids[[selected, pivot_row]]
        inverse = pow(int(matrix[pivot_row, column]), prime - 2, prime)
        matrix[pivot_row, column:] = (
            matrix[pivot_row, column:] * inverse
        ) % prime
        lower = np.flatnonzero(matrix[pivot_row + 1:, column]) + pivot_row + 1
        if len(lower):
            factors = matrix[lower, column].copy()
            matrix[lower, column:] = (
                matrix[lower, column:]
                - factors[:, None] * matrix[pivot_row, column:]
            ) % prime
        pivot_row += 1
        if pivot_row == matrix.shape[1]:
            break
    assert pivot_row == EXPECTED_COLUMNS
    return row_ids[:pivot_row]


def solve_square(
    matrix: np.ndarray,
    right_hand_sides: np.ndarray,
    prime: int,
) -> np.ndarray:
    """Solve a nonsingular modular system against several right-hand sides."""
    matrix = matrix.copy()
    solution = right_hand_sides.copy()
    size = matrix.shape[0]
    assert matrix.shape == (size, size)
    assert solution.shape[0] == size

    for column in range(size):
        candidates = np.flatnonzero(matrix[column:, column])
        assert len(candidates)
        selected = column + int(candidates[0])
        if selected != column:
            matrix[[column, selected]] = matrix[[selected, column]]
            solution[[column, selected]] = solution[[selected, column]]
        inverse = pow(int(matrix[column, column]), prime - 2, prime)
        matrix[column, column:] = matrix[column, column:] * inverse % prime
        solution[column] = solution[column] * inverse % prime
        lower = np.flatnonzero(matrix[column + 1:, column]) + column + 1
        if len(lower):
            factors = matrix[lower, column].copy()
            matrix[lower, column:] = (
                matrix[lower, column:]
                - factors[:, None] * matrix[column, column:]
            ) % prime
            solution[lower] = (
                solution[lower] - factors[:, None] * solution[column]
            ) % prime

    for column in range(size - 1, 0, -1):
        solution[:column] = (
            solution[:column]
            - matrix[:column, column, None] * solution[column]
        ) % prime
    return solution


def assignment_sha256(prime: int, labels: Sequence[int]) -> str:
    encoded = prime.to_bytes(2, "little") + b"".join(
        (int(label) % prime).to_bytes(2, "little") for label in labels
    )
    return hashlib.sha256(encoded).hexdigest()


def row_set_sha256(prime: int, row_indices: np.ndarray) -> str:
    encoded = prime.to_bytes(2, "little") + b"".join(
        int(row).to_bytes(2, "little") for row in row_indices
    )
    return hashlib.sha256(encoded).hexdigest()


def audit_assignment(
    prime: int,
    name: str,
    family: str,
    labels: Sequence[int],
    witness_rows: np.ndarray,
) -> dict[str, object]:
    matrix = base.divided_difference_matrix(prime, labels)
    minor_rank = base.modular_rank(matrix[witness_rows], prime)
    if minor_rank == EXPECTED_COLUMNS:
        rank = EXPECTED_COLUMNS
        certificate = "fixed_baseline_minor"
    else:
        rank = base.modular_rank(matrix, prime)
        certificate = "full_matrix_fallback"
    result: dict[str, object] = {
        "name": name,
        "family": family,
        "assignment_sha256": assignment_sha256(prime, labels),
        "fixed_minor_rank": minor_rank,
        "full_matrix_rank": rank,
        "nullity": EXPECTED_COLUMNS - rank,
        "certificate": certificate,
    }
    if rank < EXPECTED_COLUMNS:
        result["rank_drop_labels"] = [int(label) % prime for label in labels]
    return result


def exhaustive_tail_scan(
    prime: int,
    event: int,
    baseline_matrix: np.ndarray,
    witness_rows: np.ndarray,
) -> dict[str, object]:
    baseline_labels = list(range(base.M))
    baseline_minor = baseline_matrix[witness_rows]
    alternate_labels = baseline_labels.copy()
    alternate_labels[event] = base.M
    step = (base.M - event) % prime
    assert step
    unit_difference = (
        base.divided_difference_matrix(prime, alternate_labels)[witness_rows]
        - baseline_minor
    ) % prime
    unit_difference = unit_difference * pow(step, prime - 2, prime) % prime

    # Check the asserted affine dependence at a second unused field value.
    check_labels = baseline_labels.copy()
    check_labels[event] = base.M + 1
    check_difference = (
        base.divided_difference_matrix(prime, check_labels)[witness_rows]
        - baseline_minor
    ) % prime
    assert np.array_equal(
        check_difference,
        ((base.M + 1 - event) * unit_difference) % prime,
    )

    changed_rows = np.flatnonzero(np.any(unit_difference, axis=1))
    selectors = np.zeros(
        (EXPECTED_COLUMNS, len(changed_rows)), dtype=np.int64
    )
    selectors[changed_rows, np.arange(len(changed_rows))] = 1
    inverse_columns = solve_square(baseline_minor, selectors, prime)
    assert np.array_equal(
        baseline_minor.dot(inverse_columns) % prime,
        selectors,
    )
    update_kernel = (
        unit_difference[changed_rows].dot(inverse_columns) % prime
    )

    admissible_values = [event, *range(base.M, prime)]
    singular_minor_values = []
    fallback_results = []
    identity = np.eye(len(changed_rows), dtype=np.int64)
    for value in admissible_values:
        determinant_lemma_matrix = (
            identity + (value - event) * update_kernel
        ) % prime
        small_rank = base.modular_rank(determinant_lemma_matrix, prime)
        if small_rank == len(changed_rows):
            continue
        singular_minor_values.append(value)
        labels = baseline_labels.copy()
        labels[event] = value
        matrix = base.divided_difference_matrix(prime, labels)
        minor_rank = base.modular_rank(matrix[witness_rows], prime)
        full_rank = base.modular_rank(matrix, prime)
        assert minor_rank < EXPECTED_COLUMNS
        fallback = {
            "label_value": value,
            "determinant_lemma_rank": small_rank,
            "fixed_minor_rank": minor_rank,
            "full_matrix_rank": full_rank,
            "nullity": EXPECTED_COLUMNS - full_rank,
            "assignment_sha256": assignment_sha256(prime, labels),
        }
        if full_rank < EXPECTED_COLUMNS:
            fallback["rank_drop_labels"] = labels
        fallback_results.append(fallback)

    rank_drop_count = sum(
        result["full_matrix_rank"] < EXPECTED_COLUMNS
        for result in fallback_results
    )
    return {
        "varied_event": event,
        "fixed_labels": (
            f"gamma_i=i for i != {event}; gamma_{event} ranges over the "
            "field excluding the other 64 labels"
        ),
        "admissible_value_count": len(admissible_values),
        "changed_rows_in_fixed_minor": len(changed_rows),
        "singular_fixed_minor_value_count": len(singular_minor_values),
        "singular_fixed_minor_values": singular_minor_values,
        "fallback_results": fallback_results,
        "rank_drop_count": rank_drop_count,
    }


def field_audit(prime: int) -> dict[str, object]:
    baseline_labels = list(range(base.M))
    baseline_matrix = base.divided_difference_matrix(prime, baseline_labels)
    witness_rows = independent_row_indices(baseline_matrix, prime)
    assert base.modular_rank(baseline_matrix[witness_rows], prime) == EXPECTED_COLUMNS

    field_seed, pseudorandom = random_cases(prime)
    cases = deterministic_cases(prime) + pseudorandom
    assert len({name for name, _, _ in cases}) == len(cases)
    results = [
        audit_assignment(prime, name, family, labels, witness_rows)
        for name, family, labels in cases
    ]
    family_counts: dict[str, int] = {}
    for result in results:
        family = str(result["family"])
        family_counts[family] = family_counts.get(family, 0) + 1

    tail_scans = [
        exhaustive_tail_scan(
            prime, event, baseline_matrix, witness_rows
        )
        for event in TAIL_EVENTS
    ]
    return {
        "field_order": prime,
        "field_seed_hex": f"0x{field_seed:016x}",
        "rows": int(baseline_matrix.shape[0]),
        "columns_after_global_pencil_gauge": int(baseline_matrix.shape[1]),
        "fixed_baseline_minor_row_sha256": row_set_sha256(prime, witness_rows),
        "sampled_assignment_count": len(results),
        "sampled_family_counts": family_counts,
        "sampled_minimum_rank": min(
            int(result["full_matrix_rank"]) for result in results
        ),
        "sampled_rank_drop_count": sum(
            result["full_matrix_rank"] < EXPECTED_COLUMNS
            for result in results
        ),
        "sampled_fixed_minor_fallback_count": sum(
            result["certificate"] == "full_matrix_fallback"
            for result in results
        ),
        "sampled_assignments": results,
        "exhaustive_single_label_scans": tail_scans,
        "exhaustive_admissible_assignment_count_with_repetitions": sum(
            int(scan["admissible_value_count"]) for scan in tail_scans
        ),
        "exhaustive_rank_drop_count": sum(
            int(scan["rank_drop_count"]) for scan in tail_scans
        ),
    }


def main() -> None:
    support_hash = base.exact_incidence_audit()["family_sha256"]
    report: dict[str, object] = {
        "scope": (
            "exact label-sensitivity checks for one fixed 65-event support "
            "family over three small fields; not a label-uniform, "
            "Reed--Solomon, or delta-star theorem"
        ),
        "mathematical_scope": (
            "For each tested characteristic, the baseline nonsingular minor "
            "is a nonzero polynomial in the labels, so full column rank holds "
            "on a nonempty Zariski-open set. This generic statement does not "
            "imply full rank at every pairwise-distinct finite-field tuple."
        ),
        "support_family_sha256": support_hash,
        "master_seed_hex": f"0x{MASTER_SEED:016x}",
        "prng": (
            "SplitMix64 with the constants in this probe; field seed is "
            "master_seed XOR field_order"
        ),
        "random_case_counts_per_field": {
            "consecutive_permutations": RANDOM_PERMUTATIONS,
            "field_injections": RANDOM_INJECTIONS,
            "zero_union_mu64_permutations": RANDOM_SUBGROUP_PERMUTATIONS,
        },
        "fields": [field_audit(prime) for prime in PRIMES],
    }
    fields = report["fields"]
    assert isinstance(fields, list)
    report["summary"] = {
        "sampled_assignment_count": sum(
            int(field["sampled_assignment_count"]) for field in fields
        ),
        "sampled_rank_drop_count": sum(
            int(field["sampled_rank_drop_count"]) for field in fields
        ),
        "sampled_fixed_minor_fallback_count": sum(
            int(field["sampled_fixed_minor_fallback_count"])
            for field in fields
        ),
        "exhaustive_admissible_assignment_count_with_repetitions": sum(
            int(field["exhaustive_admissible_assignment_count_with_repetitions"])
            for field in fields
        ),
        "exhaustive_rank_drop_count": sum(
            int(field["exhaustive_rank_drop_count"]) for field in fields
        ),
    }
    canonical = json.dumps(
        report, sort_keys=True, separators=(",", ":")
    ).encode()
    report["report_sha256"] = hashlib.sha256(canonical).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
