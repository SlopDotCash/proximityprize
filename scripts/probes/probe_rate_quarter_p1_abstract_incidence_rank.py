#!/usr/bin/env python3
"""Abstract P1 predecessor countermodel and divided-difference rank probe.

This probe has two deliberately separate parts.

1. It verifies a finite set/source-line incidence system at the exact `m = 4`
   analogue of the P1 predecessor parameters:

       N = 64, K = 16, T = 36, M = N + 1.

   Every pair is declared to be its own two-point source line, with joint core
   equal to the intersection of its two agreement sets.  The checks cover the
   current pair/core/packing consequences, but not polynomial realizability.

2. It forms the support-dependent Reed--Solomon divided-difference matrix for
   consecutive labels and five deterministic random distinct-label samples
   per field.  After quotienting the `2K`-dimensional globally joint pencils,
   exact modular elimination shows
   full column rank over smooth order-64 domains in `F_193`, `F_257`, and
   `F_449`.  Thus this support family has only the joint solution for those
   tested domains and all 18 tested labellings.  The computation is not a
   uniform theorem over all choices of 65 distinct scalar labels.

The final section reproduces a Hoeffding union bound proving that the same
abstract two-point-line model exists at the literal P1 cardinalities.  This is
a barrier for incidence-only arguments, not a theorem about Reed--Solomon
stacks or delta star.

Requires NumPy.  Deterministic; runtime is under a minute on a laptop.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
from collections.abc import Sequence
from fractions import Fraction

import numpy as np


MASKS = [
    17638206544519069472, 11554406460510997939, 16869425085155136477,
    18316862300658194340, 11814277902951378822, 4030600692829884572,
    10693788503108641564, 8043370511588797483, 13157948963193711023,
    8517932655144220157, 8930612518551840049, 15586574314319114479,
    16532134047483197038, 15777898810691490119, 6736638370855526859,
    11938256448063907302, 8734429745215367518, 11374083224662382158,
    13702689566072613895, 4247374897439439952, 13639397414454057169,
    18103077160380483218, 8035624013947535129, 1831083902456808429,
    665826885445353254, 2736540990544985851, 13082190855330066772,
    5691393299973970142, 2760651233697852589, 13548457631969185524,
    16771367800990778556, 12806762755660232650, 11312524310729911191,
    6859509930918306149, 14911499131689621567, 4250459765588075504,
    18310810773023079531, 9972561195050955931, 6327573792038010852,
    17442003810759917452, 7823806304747724743, 8033995463881757700,
    14592619205590108790, 4702518559219456883, 14496083319432924920,
    13800954034418949587, 13850309925943178835, 8325464460013893534,
    14809445850592182170, 1917378056371434952, 18359837681608389241,
    3593552962482723575, 17636344593540361946, 231280068969093610,
    6896687228624243377, 1667210920233331375, 15553911506718321521,
    14544167383910132095, 4131915600210947893, 5718234193589177660,
    4892418700177218556, 427819623010489875, 9312222901073327417,
    13537947808151194573, 11782310251108664895,
]

N = 64
M = 65
K = 16
T = 36
A1STAR = 20
STRUCTURED_DIRECTION = (1 << (A1STAR + 1)) - 1


def exact_incidence_audit() -> dict[str, object]:
    assert len(MASKS) == M
    sizes = [mask.bit_count() for mask in MASKS]
    assert sizes == [T] * M

    pairs = list(itertools.combinations(range(M), 2))
    pair_cores = [MASKS[i] & MASKS[j] for i, j in pairs]
    pair_sizes = [core.bit_count() for core in pair_cores]
    coordinate_multiplicities = [
        sum((mask >> coordinate) & 1 for mask in MASKS)
        for coordinate in range(N)
    ]
    triple_sizes = [
        (MASKS[i] & MASKS[j] & MASKS[k]).bit_count()
        for i, j, k in itertools.combinations(range(M), 3)
    ]
    structured_pair_sizes = [
        (STRUCTURED_DIRECTION & core).bit_count() for core in pair_cores
    ]
    packing_lhs = [2 * max(1, T - z) + z for z in pair_sizes]

    assert M == N + 1
    assert min(pair_sizes) >= 2 * T - N
    assert max(pair_sizes) <= T - 2
    assert max(packing_lhs) <= N
    assert max(triple_sizes) <= K - 1
    assert max(structured_pair_sizes) <= K - 1
    assert STRUCTURED_DIRECTION.bit_count() == A1STAR + 1

    # A fourfold intersection of event sets is contained in every associated
    # triple intersection.  Hence the triple cap checks intersections of cores
    # for both adjacent and disjoint two-point lines.
    assert 2 * len(pairs) == M * (M - 1)

    thin_edges = [
        (i, j) for (i, j), z in zip(pairs, pair_sizes, strict=True) if z < K
    ]
    thin_adjacency = [set() for _ in range(M)]
    for i, j in thin_edges:
        thin_adjacency[i].add(j)
        thin_adjacency[j].add(i)
    thin_triangles = [
        (i, j, k)
        for i, j, k in itertools.combinations(range(M), 3)
        if j in thin_adjacency[i]
        and k in thin_adjacency[i]
        and k in thin_adjacency[j]
    ]
    assert thin_edges and not thin_triangles

    encoded = b"".join(mask.to_bytes(8, "little") for mask in MASKS)
    family_hash = hashlib.sha256(encoded).hexdigest()
    assert family_hash == (
        "4786879f2d5063f9894067cd55a313b60bcbf601eb469d640d806149f61bcfb7"
    )

    five_set_margin = 20 * T - (6 * N + 20 * (K - 1))
    assert five_set_margin > 0
    supports_by_coordinate = [
        {event for event, mask in enumerate(MASKS) if (mask >> coordinate) & 1}
        for coordinate in range(N)
    ]

    def projected_budget(labels: set[int]) -> int:
        return sum(
            min(len(labels & incident), len(incident) - 2)
            for incident in supports_by_coordinate
        )

    singleton_hall_bad = [
        event for event in range(M) if projected_budget({event}) < K
    ]
    pair_hall_bad = [
        [left, right]
        for left, right in itertools.combinations(range(M), 2)
        if projected_budget({left, right}) < 2 * K
    ]
    assert not singleton_hall_bad
    assert not pair_hall_bad
    return {
        "parameters": {"N": N, "M": M, "K": K, "T": T, "A1star": A1STAR},
        "budget_excess": M - N,
        "event_size": T,
        "coordinate_multiplicity_range": [
            min(coordinate_multiplicities), max(coordinate_multiplicities)
        ],
        "pair_core_range": [min(pair_sizes), max(pair_sizes)],
        "triple_intersection_range": [min(triple_sizes), max(triple_sizes)],
        "structured_direction_size": STRUCTURED_DIRECTION.bit_count(),
        "structured_direction_pair_core_range": [
            min(structured_pair_sizes), max(structured_pair_sizes)
        ],
        "two_point_packing_lhs_range": [min(packing_lhs), max(packing_lhs)],
        "two_point_line_count": len(pairs),
        "ordered_pair_partition_mass": 2 * len(pairs),
        "thin_edge_count": len(thin_edges),
        "thin_graph_clique_number": 2,
        "five_set_forcing_margin": five_set_margin,
        "singleton_hall_bad_count": len(singleton_hall_bad),
        "pair_hall_bad_count": len(pair_hall_bad),
        "family_sha256": family_hash,
    }


def prime_factors(value: int) -> list[int]:
    factors = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    return factors


def primitive_root(prime: int) -> int:
    factors = prime_factors(prime - 1)
    for candidate in range(2, prime):
        if all(pow(candidate, (prime - 1) // factor, prime) != 1
               for factor in factors):
            return candidate
    raise AssertionError(f"no primitive root modulo {prime}")


def divided_difference_matrix(
    prime: int,
    labels: Sequence[int] | None = None,
) -> np.ndarray:
    """Build the quotient matrix for a pairwise-distinct scalar labelling."""
    assert (prime - 1) % N == 0 and prime > M
    generator = primitive_root(prime)
    omega = pow(generator, (prime - 1) // N, prime)
    domain = [pow(omega, exponent, prime) for exponent in range(N)]
    scalar_labels = (
        list(range(M)) if labels is None
        else [int(label) % prime for label in labels]
    )
    assert len(set(domain)) == N
    assert len(scalar_labels) == M
    assert len(set(scalar_labels)) == M

    rows = []
    for coordinate, x_value in enumerate(domain):
        incident = [
            event for event, mask in enumerate(MASKS)
            if (mask >> coordinate) & 1
        ]
        assert len(incident) >= 2
        anchor_a, anchor_b = incident[:2]
        powers = np.array(
            [pow(x_value, degree, prime) for degree in range(K)],
            dtype=np.int64,
        )
        for event in incident[2:]:
            row = np.zeros((M - 2) * K, dtype=np.int64)
            coefficients = (
                (anchor_a, scalar_labels[anchor_b] - scalar_labels[event]),
                (anchor_b, scalar_labels[event] - scalar_labels[anchor_a]),
                (event, scalar_labels[anchor_a] - scalar_labels[anchor_b]),
            )
            for label, coefficient in coefficients:
                # q_0 and q_1 are the gauge-fixed global-pencil coordinates.
                if label < 2:
                    continue
                start = (label - 2) * K
                row[start:start + K] = (
                    row[start:start + K] + (coefficient % prime) * powers
                ) % prime
            rows.append(row)

    matrix = np.array(rows, dtype=np.int64)
    assert matrix.shape == (M * T - 2 * N, (M - 2) * K)
    return matrix


def modular_rank(matrix: np.ndarray, prime: int) -> int:
    """Exact row-echelon rank over F_prime, vectorized with NumPy."""
    matrix = matrix.copy()
    row_count, column_count = matrix.shape
    pivot_row = 0
    for column in range(column_count):
        candidates = np.flatnonzero(matrix[pivot_row:, column])
        if not len(candidates):
            continue
        selected = pivot_row + int(candidates[0])
        matrix[[pivot_row, selected]] = matrix[[selected, pivot_row]]
        inverse = pow(int(matrix[pivot_row, column]), prime - 2, prime)
        matrix[pivot_row, column:] = (
            matrix[pivot_row, column:] * inverse
        ) % prime
        lower_rows = np.flatnonzero(matrix[pivot_row + 1:, column]) + pivot_row + 1
        if len(lower_rows):
            factors = matrix[lower_rows, column].copy()
            matrix[lower_rows, column:] = (
                matrix[lower_rows, column:]
                - factors[:, None] * matrix[pivot_row, column:]
            ) % prime
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def exact_rank_audit() -> list[dict[str, int | bool | str]]:
    results = []
    expected_columns = (M - 2) * K
    rng = np.random.default_rng(466)
    for prime in (193, 257, 449):
        matrix = divided_difference_matrix(prime)
        rank = modular_rank(matrix, prime)
        assert rank == expected_columns
        results.append({
            "field_order": prime,
            "smooth_order_64_domain": True,
            "scalar_labels": "gamma_i=i",
            "rows": int(matrix.shape[0]),
            "columns_after_global_pencil_gauge": int(matrix.shape[1]),
            "rank": rank,
            "nullity": expected_columns - rank,
        })
        for trial in range(5):
            labels = rng.choice(prime, size=M, replace=False).tolist()
            matrix = divided_difference_matrix(prime, labels)
            rank = modular_rank(matrix, prime)
            assert rank == expected_columns
            results.append({
                "field_order": prime,
                "smooth_order_64_domain": True,
                "scalar_labels": f"seed_466_distinct_trial_{trial}",
                "rows": int(matrix.shape[0]),
                "columns_after_global_pencil_gauge": int(matrix.shape[1]),
                "rank": rank,
                "nullity": expected_columns - rank,
            })
    return results


def six_label_exhaustive_audit() -> dict[str, int | bool]:
    """Exhaust the last two labels of the first six-event subsystem over F_193."""
    prime = 193
    event_ids = list(range(6))
    generator = primitive_root(prime)
    omega = pow(generator, (prime - 1) // N, prime)
    domain = [pow(omega, exponent, prime) for exponent in range(N)]
    event_position = {event: position for position, event in enumerate(event_ids)}
    templates = []
    for coordinate, x_value in enumerate(domain):
        incident = [
            event for event in event_ids
            if (MASKS[event] >> coordinate) & 1
        ]
        if len(incident) < 3:
            continue
        anchor_a, anchor_b = incident[:2]
        powers = np.array(
            [pow(x_value, degree, prime) for degree in range(K)],
            dtype=np.int64,
        )
        for event in incident[2:]:
            templates.append((anchor_a, anchor_b, event, powers))

    def subsystem_matrix(labels: list[int]) -> np.ndarray:
        rows = []
        for anchor_a, anchor_b, event, powers in templates:
            row = np.zeros(4 * K, dtype=np.int64)
            coefficients = (
                (anchor_a, labels[anchor_b] - labels[event]),
                (anchor_b, labels[event] - labels[anchor_a]),
                (event, labels[anchor_a] - labels[anchor_b]),
            )
            for label, coefficient in coefficients:
                position = event_position[label]
                if position < 2:
                    continue
                start = (position - 2) * K
                row[start:start + K] = (
                    row[start:start + K] + (coefficient % prime) * powers
                ) % prime
            rows.append(row)
        return np.array(rows, dtype=np.int64)

    def modular_det(matrix: np.ndarray) -> int:
        matrix = matrix.copy()
        value = 1
        for column in range(matrix.shape[1]):
            candidates = np.flatnonzero(matrix[column:, column])
            if not len(candidates):
                return 0
            selected = column + int(candidates[0])
            if selected != column:
                matrix[[column, selected]] = matrix[[selected, column]]
                value = -value
            pivot = int(matrix[column, column])
            value = (value * pivot) % prime
            inverse = pow(pivot, prime - 2, prime)
            matrix[column, column:] = (
                matrix[column, column:] * inverse
            ) % prime
            lower_rows = np.flatnonzero(matrix[column + 1:, column]) + column + 1
            if len(lower_rows):
                factors = matrix[lower_rows, column].copy()
                matrix[lower_rows, column:] = (
                    matrix[lower_rows, column:]
                    - factors[:, None] * matrix[column, column:]
                ) % prime
        return value % prime

    # These three 64-row minors share rows 0..62.  Rows 63,64,65 are the
    # point-3/4/5 constraints in the same coordinate-44 local block.
    minor_rows = [list(range(63)) + [last] for last in (63, 64, 65)]

    candidates = [value for value in range(prime) if value not in (0, 1, 2, 3)]
    tested = 0
    first_minor_zeros = 0
    first_two_common_zeros = 0
    all_three_common_zeros = 0
    for label_four in candidates:
        for label_five in candidates:
            if label_four == label_five:
                continue
            tested += 1
            matrix = subsystem_matrix([0, 1, 2, 3, label_four, label_five])
            determinants = [modular_det(matrix[rows, :]) for rows in minor_rows]
            first_minor_zeros += determinants[0] == 0
            first_two_common_zeros += determinants[0] == 0 and determinants[1] == 0
            all_three_common_zeros += all(value == 0 for value in determinants)
            assert any(value != 0 for value in determinants)
    assert tested == 35532
    assert (first_minor_zeros, first_two_common_zeros, all_three_common_zeros) == (189, 1, 0)
    return {
        "field_order": prime,
        "event_count": len(event_ids),
        "fixed_labels": 4,
        "exhausted_distinct_ordered_pairs": tested,
        "columns_after_global_pencil_gauge": 4 * K,
        "adjacent_minor_common_zero_counts": [
            first_minor_zeros, first_two_common_zeros, all_three_common_zeros
        ],
        "all_full_rank": True,
    }


def hoeffding_log10(count: int, trials: int, gap: Fraction) -> float:
    assert gap > 0
    return math.log10(count) - float(2 * gap * gap / trials) / math.log(10)


def p1_probabilistic_barrier() -> dict[str, object]:
    n = 2 ** 30
    event_count = n + 1
    k = 2 ** 28
    threshold = 592_794_966
    a1star = 327_272_220
    structured_size = a1star + 1
    probability = Fraction(9, 16)
    pair_probability = probability ** 2
    triple_probability = probability ** 3

    terms = {
        "some_event_has_size_below_T": hoeffding_log10(
            event_count, n, probability * n - threshold
        ),
        "some_pair_core_exceeds_T_minus_2": hoeffding_log10(
            math.comb(event_count, 2), n,
            (threshold - 1) - pair_probability * n,
        ),
        "some_distinct_line_cores_meet_in_K_via_a_triple": hoeffding_log10(
            math.comb(event_count, 3), n,
            k - triple_probability * n,
        ),
        "structured_direction_meets_some_pair_core_in_K": hoeffding_log10(
            math.comb(event_count, 2), structured_size,
            k - pair_probability * structured_size,
        ),
    }
    largest = max(terms.values())
    total = largest + math.log10(sum(10 ** (term - largest)
                                         for term in terms.values()))
    assert total < 0
    return {
        "parameters": {
            "N": n, "M": event_count, "K": k, "T": threshold,
            "A1star": a1star,
        },
        "bernoulli_probability": str(probability),
        "means": {
            "event_size": str(probability * n),
            "pair_core": str(pair_probability * n),
            "triple_core": str(triple_probability * n),
            "structured_direction_pair_core": str(
                pair_probability * structured_size
            ),
        },
        "log10_hoeffding_union_terms": terms,
        "log10_total_failure_upper_bound": total,
        "five_set_forcing_margin": (
            20 * threshold - (6 * n + 20 * (k - 1))
        ),
    }


def main() -> None:
    report = {
        "scope": (
            "abstract incidence barrier plus finite computational rank checks "
            "with sampled and partially exhausted scalar labels; not a "
            "label-uniform, Reed-Solomon, or delta-star theorem"
        ),
        "exact_abstract_miniature": exact_incidence_audit(),
        "exact_divided_difference_ranks": exact_rank_audit(),
        "six_label_exhaustive_rank": six_label_exhaustive_audit(),
        "literal_P1_probabilistic_barrier": p1_probabilistic_barrier(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
