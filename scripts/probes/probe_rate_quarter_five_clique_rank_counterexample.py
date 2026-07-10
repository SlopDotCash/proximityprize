#!/usr/bin/env python3
"""Exact mixed-support falsifier for universal five-clique pencil collapse.

At the ratio-faithful P1 miniature ``n=32, k=8, t=18``, the support design
below has five vertices of degree 18, every pair has codegree at least 8, and
every triple has codegree at most 7.  Nevertheless its concurrency matrix has
rank 23, one below the pencil-only rank 24.  The final checks search the exact
17-dimensional kernel first for a genuine no-three-collinear realization and
then for the weaker but decisive non-single-pencil realization, running the
full clique/no-joint verifier from ``probe_w4_clique_pencil_structure``.

This refutes a support-uniform proof of ``CliqueFiveCollinear``.  It is a
small-field Reed--Solomon clique counterexample only if the final full verifier
reports a valid no-three-collinear clique; it does not by itself refute the
prize-scale bad-count statement.
"""

from __future__ import annotations

import json
import random

import probe_w4_clique_pencil_structure as w4


DESIGN: list[tuple[int, tuple[int, ...]]] = [
    (0, (0, 1)),
    (1, (1, 2, 3)),
    (2, (0, 1)),
    (3, (0, 1)),
    (4, (1, 2, 4)),
    (5, (0, 1)),
    (6, (3, 4)),
    (7, (1, 2, 4)),
    (8, (0, 4)),
    (9, (3, 4)),
    (10, (2, 3, 4)),
    (11, (1, 2, 3)),
    (12, (0, 1, 2, 3, 4)),
    (13, (1, 2, 3)),
    (14, (1, 2, 4)),
    (15, (3, 4)),
    (16, (0, 2)),
    (17, (0, 1, 2, 3, 4)),
    (18, (0, 2)),
    (19, (0, 2, 3, 4)),
    (20, (0, 1, 2, 3, 4)),
    (21, (0, 1, 3, 4)),
    (22, (3, 4)),
    (23, (0, 3)),
    (24, (0, 1)),
    (25, (0, 2)),
    (26, (1, 2, 3)),
    (27, (0, 2, 3, 4)),
    (28, (1, 2, 4)),
    (29, (0, 1)),
    (30, (0, 2, 3, 4)),
    (31, (3, 4)),
]


def incidence_profile() -> dict[str, object]:
    vertex = [0] * 5
    pair: dict[tuple[int, int], int] = {}
    triple: dict[tuple[int, int, int], int] = {}
    for _, support in DESIGN:
        for i in support:
            vertex[i] += 1
        import itertools

        for ij in itertools.combinations(support, 2):
            pair[ij] = pair.get(ij, 0) + 1
        for ijk in itertools.combinations(support, 3):
            triple[ijk] = triple.get(ijk, 0) + 1
    return {
        "vertex_degrees": vertex,
        "pair_codegrees": {str(key): value for key, value in pair.items()},
        "triple_codegrees": {str(key): value for key, value in triple.items()},
        "minimum_pair_codegree": min(pair.values()),
        "maximum_triple_codegree": max(triple.values()),
    }


def main() -> None:
    assert w4.design_counts_ok(5, DESIGN)
    gammas = [3 + 6 * i for i in range(5)]
    rows = w4.concurrency_system(5, gammas, DESIGN)
    rank, basis = w4.rref_mod_p(rows)
    assert rank == 23

    result = w4.try_general_position(
        5,
        0,
        samples=5000,
        design=DESIGN,
        tag_suffix="_rank23_mixed_support",
    )

    # The one-dimensional excess over the pencil locus may force a smaller
    # collinear subconfiguration, so search separately for the exact property
    # needed to refute five-collinear collapse: valid, distinct, but not all
    # five points on one pencil.
    random.seed(0x4665C1A)
    nonpencil_realized = None
    nonpencil_certificate = None
    for _ in range(5000):
        coefficient_vector = [0] * (5 * w4.KDIM)
        for vector in basis:
            scalar = random.randrange(w4.P)
            for column in range(5 * w4.KDIM):
                coefficient_vector[column] = (
                    coefficient_vector[column] + scalar * vector[column]
                ) % w4.P
        polynomials = [
            coefficient_vector[i * w4.KDIM : (i + 1) * w4.KDIM]
            for i in range(5)
        ]
        if len({tuple(polynomial) for polynomial in polynomials}) < 5:
            continue
        base_slope = w4.slope_poly(
            gammas[0], polynomials[0], gammas[1], polynomials[1]
        )
        all_five_collinear = all(
            w4.poly_is_zero(
                w4.poly_sub(
                    base_slope,
                    w4.slope_poly(
                        gammas[0], polynomials[0], gammas[i], polynomials[i]
                    ),
                )
            )
            for i in range(2, 5)
        )
        if all_five_collinear:
            continue

        u0, u1 = [1] * w4.N, [0] * w4.N
        for coordinate, support in DESIGN:
            i0, i1 = support[0], support[1]
            x = w4.XS[coordinate]
            value0 = w4.poly_eval(polynomials[i0], x)
            value1 = w4.poly_eval(polynomials[i1], x)
            slope = (
                (value1 - value0) * w4.inv(gammas[i1] - gammas[i0])
            ) % w4.P
            u1[coordinate] = slope
            u0[coordinate] = (value0 - gammas[i0] * slope) % w4.P
        verification = w4.verify_clique(
            "rank23_mixed_support_nonpencil",
            gammas,
            polynomials,
            u0,
            u1,
            expect_no3collinear=False,
        )
        if verification["is_valid_clique"]:
            nonpencil_realized = verification
            nonpencil_certificate = {
                "polynomial_coefficients": polynomials,
                "received_u0": u0,
                "received_u1": u1,
            }
            break
    report = {
        "field": w4.P,
        "n": w4.N,
        "k": w4.KDIM,
        "agreement_threshold": w4.TVERT,
        "labels": gammas,
        "constraint_count": len(rows),
        "rank": rank,
        "kernel_dimension": 5 * w4.KDIM - rank,
        "pencil_locus_dimension": 2 * w4.KDIM,
        "incidence": incidence_profile(),
        "general_position_sample_found": result.get(
            "general_position_sample_found", False
        ),
        "realized_clique_valid": result.get("realized_clique_valid", False),
        "realized_no3collinear": result.get("realized_no3collinear", False),
        "realized": result.get("realized"),
        "nonpencil_sample_found": nonpencil_realized is not None,
        "nonpencil_realized": nonpencil_realized,
        "nonpencil_certificate": nonpencil_certificate,
        "scope": (
            "ratio-faithful n=32 Reed--Solomon clique falsifier; not a "
            "prize-scale bad-count counterexample"
        ),
    }
    print(json.dumps(report, indent=2, sort_keys=True))

    assert report["nonpencil_sample_found"]
    print("probe_rate_quarter_five_clique_rank_counterexample: PASS")


if __name__ == "__main__":
    main()
