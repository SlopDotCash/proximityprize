#!/usr/bin/env python3
"""Exact leaf/core decomposition of the fixed P1 rank witness minor.

This probe refines ``probe_rate_quarter_p1_label_sensitivity.py`` for the
single 1008-row witness minor selected from the fixed 65-event support family
in ``probe_rate_quarter_p1_abstract_incidence_rank.py``.

Every divided-difference row is supported on three event blocks.  In the
selected minor, 45 event blocks are combinatorial leaves: each occurs in
exactly ``K = 16`` rows, its 16 coordinates are distinct, and the 45 row
supports are pairwise disjoint.  Permuting those rows and columns first gives

    [ blockdiag(diag(anchor differences) * Vandermonde)   * ]
    [                         0                         core ]

with a 720-by-720 leaf block and a 288-by-288 core.  Consequently the
determinant is independent of every leaf label, including at colliding label
values, and factors into 45 ordinary Vandermonde determinants, 720 anchor
differences, and the core determinant.

For each of F_193, F_257, and F_449 the probe also constructs every one-label
update kernel ``D_e B^{-1}`` on its changed rows.  Leaf kernels are exactly
zero.  Every core kernel has a nonzero trace-of-a-power witness and is
therefore nonnilpotent, proving that the corresponding one-variable slice of
the fixed minor determinant is nonconstant in each tested field.  Exhaustive
core-slice root scans find roots away from the core anchor labels, refuting a
pure anchor-difference factorization of the residual.  Full elimination at
all 29 pairwise-distinct such roots shows that other rows repair the fixed
minor: the full operator remains rank 1008 in every case.

This is a structural theorem about one selected minor of one fixed support
family.  It is not a rank theorem for arbitrary supports or a proof of the P1
predecessor residual.

Requires NumPy.  Deterministic; expected runtime is under two minutes.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from collections.abc import Sequence

import numpy as np

import probe_rate_quarter_p1_abstract_incidence_rank as base
import probe_rate_quarter_p1_label_sensitivity as sensitivity


PRIMES = (193, 257, 449)
EVENTS = tuple(range(2, base.M))
EXPECTED_LEAVES = (
    7, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29,
    31, 32, 33, 35, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
)
EXPECTED_CORE = (
    2, 3, 4, 5, 6, 8, 9, 11, 12, 23, 24, 25, 26, 30, 34, 36, 39, 48,
)
EXPECTED_FACTOR_EXPONENTS = {
    (0, 1): 180,
    (0, 2): 76,
    (0, 3): 29,
    (0, 4): 24,
    (0, 6): 22,
    (1, 2): 166,
    (1, 3): 27,
    (1, 4): 43,
    (2, 3): 19,
    (2, 5): 46,
    (2, 9): 25,
    (3, 4): 24,
    (3, 6): 28,
    (4, 6): 11,
}
EXPECTED_WITNESS_ROWS_SHA256 = (
    "0f6a934ff4a6c10b3d2c36f0bc8e3b639284bddd7ec20113467d3edc558425d1"
)
EXPECTED_STRUCTURE_SHA256 = (
    "8c0feff5a424edd13f4f2e4d3bf314e6b244ce94d44fb00f61c5d497c0e957bb"
)
EXPECTED_UPDATE_HASHES = {
    193: "9323c927aa8504d80d4450354ae1cd39a24ce5657e574dc2b07fe991fe50a13e",
    257: "b1542aa6bfe44a478d878bfdf1da94e85840ae3f7d611fb4c0e8ef32cb954dae",
    449: "c804753147a6d482ce93cfdf4253b5be6e9e479310fb341615c5707278c3d7e3",
}
EXPECTED_CORE_ROOTS = {
    193: {
        2: (0, 1, 3, 5, 9, 82), 3: (0, 1, 2, 4, 6, 8, 78),
        4: (0, 1, 3, 8), 5: (2,), 6: (0, 3), 8: (3, 4), 9: (2,),
        11: (27, 32, 116), 12: (86,), 23: (189,), 24: (), 25: (),
        26: (2,), 30: (85,), 34: (62, 191), 36: (171,), 39: (77,), 48: (),
    },
    257: {
        2: (0, 1, 3, 5, 9, 186), 3: (0, 1, 2, 4, 6, 8, 62),
        4: (0, 1, 3, 8), 5: (2,), 6: (0, 3), 8: (3, 4), 9: (2,),
        11: (), 12: (199,), 23: (69,), 24: (178,), 25: (), 26: (226,),
        30: (95,), 34: (104, 220), 36: (4,), 39: (6,), 48: (),
    },
    449: {
        2: (0, 1, 3, 5, 9, 73), 3: (0, 1, 2, 4, 6, 8),
        4: (0, 1, 3, 8), 5: (2,), 6: (0, 3), 8: (3, 4), 9: (2,),
        11: (342,), 12: (218,), 23: (), 24: (), 25: (91,), 26: (267,),
        30: (78,), 34: (87, 430), 36: (231,), 39: (46,),
        48: (77, 156, 179),
    },
}
EXPECTED_CORE_ROOT_SCAN_HASHES = {
    193: "ffef236337774555d7d98927baa5aec024723949b1940dade038078936cb1478",
    257: "3237c00f4dcebf44b64e27fec13c8b9a7a017ed4c356e0bc81a3fc38924115ee",
    449: "365dba5b194355701d96453bb9ea7dbece74843bb9b4873bd0ada528f1083f33",
}
EXPECTED_REPORT_SHA256 = (
    "5294e9046f9d90d89ecd97541e4a9498f9f50d3c249c5eb90a8c8c101c6c9f08"
)


def all_row_metadata() -> list[tuple[int, int, int, int]]:
    """Return ``(coordinate, anchor_a, anchor_b, terminal)`` in matrix order."""
    metadata = []
    for coordinate in range(base.N):
        incident = [
            event for event, mask in enumerate(base.MASKS)
            if (mask >> coordinate) & 1
        ]
        anchor_a, anchor_b = incident[:2]
        metadata.extend(
            (coordinate, anchor_a, anchor_b, terminal)
            for terminal in incident[2:]
        )
    assert len(metadata) == base.M * base.T - 2 * base.N
    return metadata


def coefficient_pair(
    event: int,
    row: tuple[int, int, int, int],
) -> tuple[int, int]:
    """Return ``(u,v)`` when the event-block coefficient is gamma_u-gamma_v."""
    _, anchor_a, anchor_b, terminal = row
    if event == anchor_a:
        return anchor_b, terminal
    if event == anchor_b:
        return terminal, anchor_a
    assert event == terminal
    return anchor_a, anchor_b


def sha256_json(value: object) -> str:
    canonical = json.dumps(
        value, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(canonical).hexdigest()


def structural_audit(witness_rows: Sequence[int]) -> dict[str, object]:
    metadata = all_row_metadata()
    selected = [metadata[int(row)] for row in witness_rows]
    supports = {
        event: [
            local_row for local_row, (_, a, b, terminal) in enumerate(selected)
            if event in (a, b, terminal)
        ]
        for event in EVENTS
    }
    leaves = tuple(
        event for event in EVENTS
        if len(supports[event]) == base.K
        and len({selected[row][0] for row in supports[event]}) == base.K
    )
    core = tuple(event for event in EVENTS if event not in leaves)
    assert leaves == EXPECTED_LEAVES
    assert core == EXPECTED_CORE

    leaf_row_owner: dict[int, int] = {}
    for event in leaves:
        for row in supports[event]:
            assert row not in leaf_row_owner
            leaf_row_owner[row] = event
    leaf_rows = tuple(sorted(leaf_row_owner))
    core_rows = tuple(
        row for row in range(len(selected)) if row not in leaf_row_owner
    )
    assert len(leaf_rows) == len(leaves) * base.K == 720
    assert len(core_rows) == len(core) * base.K == 288

    # Pairwise-disjoint leaf supports imply that every leaf row contains one
    # leaf event and two core-or-gauge events.  Those other events give the
    # diagonal leaf-block coefficient.
    factors: Counter[tuple[int, int]] = Counter()
    for row, leaf in leaf_row_owner.items():
        pair = coefficient_pair(leaf, selected[row])
        assert pair[0] not in leaves and pair[1] not in leaves
        # Every leaf happens to be the terminal event, so no sign is hidden by
        # canonicalizing the pair for the human-readable exponent table.
        assert pair[0] < pair[1]
        factors[pair] += 1
    assert dict(factors) == EXPECTED_FACTOR_EXPONENTS
    assert sum(factors.values()) == len(leaf_rows)

    payload = {
        "witness_rows": [int(row) for row in witness_rows],
        "leaf_events": list(leaves),
        "core_events": list(core),
        "leaf_row_owner": sorted(leaf_row_owner.items()),
        "core_rows": list(core_rows),
        "factor_exponents": {
            f"{left}-{right}": exponent
            for (left, right), exponent in sorted(factors.items())
        },
    }
    result = {
        "leaf_block_count": len(leaves),
        "leaf_block_size": base.K,
        "leaf_rows": len(leaf_rows),
        "core_rows": len(core_rows),
        "leaf_events": list(leaves),
        "core_events": list(core),
        "leaf_supports_pairwise_disjoint": True,
        "leaf_coordinate_sets_pairwise_distinct_internally": True,
        "extracted_anchor_difference_degree": len(leaf_rows),
        "residual_core_degree": len(core_rows),
        "factor_exponents": payload["factor_exponents"],
        "witness_rows_sha256": sha256_json(payload["witness_rows"]),
        "structure_sha256": sha256_json(payload),
        "leaf_row_groups": {
            str(event): supports[event] for event in leaves
        },
        "core_local_rows": list(core_rows),
    }
    assert result["witness_rows_sha256"] == EXPECTED_WITNESS_ROWS_SHA256
    assert result["structure_sha256"] == EXPECTED_STRUCTURE_SHA256
    return result


def selected_derivative(
    prime: int,
    event: int,
    selected_metadata: Sequence[tuple[int, int, int, int]],
) -> np.ndarray:
    """Derivative of the fixed minor with respect to one scalar label."""
    domain = sensitivity.order_64_domain(prime)
    powers = [
        np.array(
            [pow(domain[x], degree, prime) for degree in range(base.K)],
            dtype=np.int64,
        )
        for x in range(base.N)
    ]
    derivative = np.zeros(
        (len(selected_metadata), (base.M - 2) * base.K), dtype=np.int64
    )

    def add_block(
        row: int,
        block_event: int,
        coefficient: int,
        coordinate: int,
    ) -> None:
        if block_event < 2:
            return
        start = (block_event - 2) * base.K
        derivative[row, start:start + base.K] = (
            derivative[row, start:start + base.K]
            + coefficient * powers[coordinate]
        ) % prime

    for row, (coordinate, anchor_a, anchor_b, terminal) in enumerate(
        selected_metadata
    ):
        if event == anchor_b:
            add_block(row, anchor_a, 1, coordinate)
        if event == terminal:
            add_block(row, anchor_a, -1, coordinate)
        if event == terminal:
            add_block(row, anchor_b, 1, coordinate)
        if event == anchor_a:
            add_block(row, anchor_b, -1, coordinate)
        if event == anchor_a:
            add_block(row, terminal, 1, coordinate)
        if event == anchor_b:
            add_block(row, terminal, -1, coordinate)
    return derivative


def first_nonzero_trace_power(
    matrix: np.ndarray,
    prime: int,
    limit: int = 4,
) -> tuple[int, int] | None:
    power = matrix.copy()
    for exponent in range(1, limit + 1):
        trace = int(np.trace(power) % prime)
        if trace:
            return exponent, trace
        power = power.dot(matrix) % prime
    return None


def block_columns(events: Sequence[int]) -> np.ndarray:
    return np.array(
        [
            column
            for event in events
            for column in range((event - 2) * base.K, (event - 1) * base.K)
        ],
        dtype=np.int64,
    )


def field_audit(
    prime: int,
    common_witness_rows: np.ndarray,
    structure: dict[str, object],
) -> dict[str, object]:
    baseline_labels = list(range(base.M))
    full_matrix = base.divided_difference_matrix(prime, baseline_labels)
    field_pivot_rows = sensitivity.independent_row_indices(full_matrix, prime)
    # The pivot order swaps two rows in F_257 and F_449, but the selected row
    # set is identical.  Use the F_193 ordering in every field so this really
    # is one fixed minor, up to reduction of its entries modulo the prime.
    assert np.array_equal(
        np.sort(field_pivot_rows), np.sort(common_witness_rows)
    )
    witness_rows = common_witness_rows
    minor = full_matrix[witness_rows]
    inverse = sensitivity.solve_square(
        minor, np.eye(minor.shape[0], dtype=np.int64), prime
    )
    assert np.array_equal(
        minor.dot(inverse) % prime,
        np.eye(minor.shape[0], dtype=np.int64),
    )

    metadata = all_row_metadata()
    selected = [metadata[int(row)] for row in witness_rows]
    leaf_events = tuple(int(event) for event in structure["leaf_events"])
    core_events = tuple(int(event) for event in structure["core_events"])
    leaf_groups = {
        int(event): [int(row) for row in rows]
        for event, rows in structure["leaf_row_groups"].items()
    }
    leaf_rows_ordered = np.array(
        [row for event in leaf_events for row in leaf_groups[event]],
        dtype=np.int64,
    )
    core_rows = np.array(structure["core_local_rows"], dtype=np.int64)
    leaf_columns = block_columns(leaf_events)
    core_columns = block_columns(core_events)

    assert not np.any(minor[np.ix_(core_rows, leaf_columns)])
    leaf_block = minor[np.ix_(leaf_rows_ordered, leaf_columns)]
    core_block = minor[np.ix_(core_rows, core_columns)]
    assert base.modular_rank(leaf_block, prime) == len(leaf_columns)
    assert base.modular_rank(core_block, prime) == len(core_columns)
    domain = sensitivity.order_64_domain(prime)
    for leaf_index, event in enumerate(leaf_events):
        rows = np.array(leaf_groups[event], dtype=np.int64)
        columns = block_columns((event,))
        diagonal_block = minor[np.ix_(rows, columns)]
        expected_block = np.array([
            [
                (
                    baseline_labels[coefficient_pair(event, selected[row])[0]]
                    - baseline_labels[coefficient_pair(event, selected[row])[1]]
                ) * pow(domain[selected[row][0]], degree, prime) % prime
                for degree in range(base.K)
            ]
            for row in rows
        ], dtype=np.int64)
        assert np.array_equal(diagonal_block, expected_block)
        assert base.modular_rank(diagonal_block, prime) == base.K
        before = leaf_index * base.K
        after = before + base.K
        assert np.array_equal(
            diagonal_block, leaf_block[before:after, before:after]
        )
        assert not np.any(leaf_block[before:after, :before])
        assert not np.any(leaf_block[before:after, after:])

    updates = []
    derivatives: dict[int, np.ndarray] = {}
    for event in EVENTS:
        derivative = selected_derivative(prime, event, selected)
        derivatives[event] = derivative
        changed_rows = np.flatnonzero(np.any(derivative, axis=1))
        kernel = (
            derivative[changed_rows].dot(inverse[:, changed_rows]) % prime
        )
        kernel_rank = base.modular_rank(kernel, prime)
        kernel_is_zero = not np.any(kernel)
        if event in leaf_events:
            assert kernel_is_zero and kernel_rank == 0
            state = "zero"
            trace_witness = None
        else:
            assert not kernel_is_zero
            trace_witness = first_nonzero_trace_power(kernel, prime)
            assert trace_witness is not None
            state = "nonnilpotent"
        updates.append({
            "event": event,
            "determinant_dependence": (
                "independent_by_leaf_factorization"
                if event in leaf_events
                else "nonconstant_baseline_slice"
            ),
            "changed_rows": len(changed_rows),
            "update_kernel_order": len(changed_rows),
            "update_kernel_rank": kernel_rank,
            "update_kernel_state": state,
            "first_nonzero_trace_power": (
                None if trace_witness is None else trace_witness[0]
            ),
            "first_nonzero_trace_value": (
                None if trace_witness is None else trace_witness[1]
            ),
        })

    assert [
        update["event"] for update in updates
        if update["update_kernel_state"] == "zero"
    ] == list(leaf_events)
    assert [
        update["event"] for update in updates
        if update["update_kernel_state"] == "nonnilpotent"
    ] == list(core_events)

    # Exhaust every value of each core label in the residual determinant.
    # Non-core-anchor roots prove that the 288-degree residual is not merely a
    # product of pairwise differences.  Values >= M remain distinct from all
    # other baseline labels; full elimination checks that singularity of this
    # particular minor is repaired by other rows of the 2212-row operator.
    core_inverse = sensitivity.solve_square(
        core_block, np.eye(core_block.shape[0], dtype=np.int64), prime
    )
    core_anchor_values = {0, 1, *core_events}
    core_root_scans = []
    full_matrix_fallbacks = []
    for event in core_events:
        core_derivative = derivatives[event][np.ix_(core_rows, core_columns)]
        changed_core_rows = np.flatnonzero(np.any(core_derivative, axis=1))
        assert len(changed_core_rows) < prime
        core_kernel = (
            core_derivative[changed_core_rows].dot(
                core_inverse[:, changed_core_rows]
            ) % prime
        )
        identity = np.eye(len(changed_core_rows), dtype=np.int64)
        roots = [
            value for value in range(prime)
            if base.modular_rank(
                (identity + (value - event) * core_kernel) % prime, prime
            ) < len(changed_core_rows)
        ]
        assert tuple(roots) == EXPECTED_CORE_ROOTS[prime][event]
        off_core_anchor_roots = [
            value for value in roots if value not in core_anchor_values - {event}
        ]
        admissible_distinct_roots = [
            value for value in roots if value >= base.M
        ]
        core_root_scans.append({
            "event": event,
            "slice_degree_upper_bound": len(changed_core_rows),
            "core_update_kernel_rank": base.modular_rank(core_kernel, prime),
            "roots": roots,
            "off_core_anchor_roots": off_core_anchor_roots,
            "admissible_distinct_roots": admissible_distinct_roots,
        })
        for value in admissible_distinct_roots:
            labels = baseline_labels.copy()
            labels[event] = value
            matrix = base.divided_difference_matrix(prime, labels)
            rank = base.modular_rank(matrix, prime)
            fixed_minor_rank = base.modular_rank(matrix[witness_rows], prime)
            assert fixed_minor_rank == (base.M - 2) * base.K - 1
            assert rank == (base.M - 2) * base.K
            full_matrix_fallbacks.append({
                "event": event,
                "replacement_label": value,
                "fixed_minor_rank": fixed_minor_rank,
                "full_matrix_rank": rank,
                "full_matrix_nullity": (base.M - 2) * base.K - rank,
                "assignment_sha256": sensitivity.assignment_sha256(prime, labels),
            })
    assert any(scan["off_core_anchor_roots"] for scan in core_root_scans)
    assert full_matrix_fallbacks
    assert len(full_matrix_fallbacks) == {193: 9, 257: 8, 449: 12}[prime]

    # Independently validate the symbolic derivative formula for every event
    # in one characteristic.  The alternate value 65 is unused and distinct.
    if prime == PRIMES[0]:
        for event in EVENTS:
            labels = baseline_labels.copy()
            labels[event] = base.M
            finite_difference = (
                base.divided_difference_matrix(prime, labels)[witness_rows]
                - minor
            ) % prime
            scale = (base.M - event) % prime
            derivative = selected_derivative(prime, event, selected)
            assert np.array_equal(finite_difference, scale * derivative % prime)

    update_payload = [
        {
            key: value for key, value in update.items()
            if key != "determinant_dependence"
        }
        for update in updates
    ]
    result = {
        "field_order": prime,
        "fixed_minor_rank": base.modular_rank(minor, prime),
        "leaf_block_rank": base.modular_rank(leaf_block, prime),
        "core_block_rank": base.modular_rank(core_block, prime),
        "zero_update_events": list(leaf_events),
        "nonnilpotent_update_events": list(core_events),
        "nonzero_nilpotent_update_events": [],
        "collision_values_covered_for_leaf_events": True,
        "core_is_pure_anchor_difference_product": False,
        "core_root_scans": core_root_scans,
        "core_root_scans_sha256": sha256_json(core_root_scans),
        "admissible_singular_minor_full_matrix_fallbacks": full_matrix_fallbacks,
        "updates": updates,
        "updates_sha256": sha256_json(update_payload),
    }
    assert result["updates_sha256"] == EXPECTED_UPDATE_HASHES[prime]
    assert (
        result["core_root_scans_sha256"]
        == EXPECTED_CORE_ROOT_SCAN_HASHES[prime]
    )
    return result


def main() -> None:
    baseline = base.divided_difference_matrix(PRIMES[0], list(range(base.M)))
    witness_rows = sensitivity.independent_row_indices(baseline, PRIMES[0])
    structure = structural_audit(witness_rows)
    fields = [field_audit(prime, witness_rows, structure) for prime in PRIMES]

    report: dict[str, object] = {
        "scope": (
            "one fixed 1008-row minor of one fixed 65-event support family; "
            "not a universal rank, Reed--Solomon, predecessor, or delta-star theorem"
        ),
        "support_family_sha256": base.exact_incidence_audit()["family_sha256"],
        "parameters": {
            "N": base.N,
            "M": base.M,
            "K": base.K,
            "minor_order": (base.M - 2) * base.K,
        },
        "structural_factorization": structure,
        "theorem_sized_condition": (
            "For a square block-Vandermonde minor with K columns per event, "
            "if a set L of event blocks each occurs in exactly K selected "
            "rows, those row supports are pairwise disjoint, and each block's "
            "K coordinates are distinct, then row/column permutation makes "
            "the L part block upper triangular. Its determinant is the "
            "residual determinant times one ordinary Vandermonde and K "
            "opposite-label differences per leaf. In particular it is "
            "independent of every leaf label."
        ),
        "fields": fields,
        "summary": {
            "field_orders": list(PRIMES),
            "algebraically_label_independent_events": list(EXPECTED_LEAVES),
            "fieldwise_nonconstant_slice_events": list(EXPECTED_CORE),
            "zero_update_kernel_count_per_field": len(EXPECTED_LEAVES),
            "nonnilpotent_update_kernel_count_per_field": len(EXPECTED_CORE),
            "nonzero_nilpotent_update_kernel_count_per_field": 0,
            "factorization": (
                "det(minor) = nonzero domain constant * "
                "product(anchor differences with recorded exponents) * "
                "det(288x288 core), up to row/column permutation sign"
            ),
            "core_is_pure_anchor_difference_product": False,
            "admissible_singular_minor_assignments_checked_by_full_elimination": sum(
                len(field["admissible_singular_minor_full_matrix_fallbacks"])
                for field in fields
            ),
            "full_operator_rank_drops_at_those_assignments": 0,
        },
    }
    canonical = json.dumps(
        report, sort_keys=True, separators=(",", ":")
    ).encode()
    report["report_sha256"] = hashlib.sha256(canonical).hexdigest()
    assert report["report_sha256"] == EXPECTED_REPORT_SHA256
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
