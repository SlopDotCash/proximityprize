#!/usr/bin/env python3
"""Exact general-position five-clique over an adversarial RS evaluation set.

This certificate is stronger than the earlier 4+1 witness.  Over F_10007 it
gives an [32,8] Reed--Solomon evaluation code, a two-row received stack, and
five distinct scalar explanations such that

* every explanation agrees on at least 18 coordinates;
* every pair overlaps on at least 8 coordinates;
* no explanation is jointly explained by two degree-<8 polynomials on its
  agreement set; and
* none of the ten triples of lifted polynomial points is collinear.

Thus the domain-uniform local claim "every five overlap-clique contains four
collinear points" is false.  The evaluation coordinates were reverse-built
from roots of the ten divided-difference polynomials.  This does not refute a
claim restricted to the canonical roots-of-unity domain.
"""

from __future__ import annotations

import itertools
import json

import probe_w4_clique_pencil_structure as w4


P = 10007
N = 32
K = 8
T = 18
GAMMAS = [3, 9, 15, 21, 27]

COORDINATES = [
    1, 2, 109, 3738, 2592, 9206, 3028, 5102,
    8396, 133, 5572, 9119, 296, 7925, 1262, 8203,
    9286, 3588, 7455, 3137, 3240, 9894, 4848, 8129,
    3, 4, 5, 6, 7, 8, 9, 10,
]

POLYNOMIALS = [
    [0],
    [0],
    [3469, 8544, 7394, 7201, 8415, 3545, 4258, 7209],
    [4999, 3339, 7239, 2762, 5716, 2814, 5273, 7886],
    [9604, 2689, 4610, 3873, 278, 8888, 6616, 3470],
]

RECEIVED_U0 = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2832, 9628, 3767, 2777, 1048, 7019, 6957,
    5917, 5321, 2304, 9202, 6496, 3740, 6298, 9975, 0, 3788, 4925, 5223,
    4839, 5049, 530, 4132,
]

RECEIVED_U1 = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 9063, 3462, 2080, 2410, 6322, 332, 9234,
    4902, 7192, 9751, 4537, 1502, 4032, 3345, 8040, 0, 2073, 1694, 8266,
    8394, 1377, 660, 6622,
]


def evaluate(poly: list[int], x: int) -> int:
    value = 0
    for coefficient in reversed(poly):
        value = (value * x + coefficient) % P
    return value


def interpolate(points: list[tuple[int, int]]) -> list[int]:
    """Lagrange interpolation over F_P, independent of w4.XS."""
    result = [0] * len(points)
    for i, (xi, yi) in enumerate(points):
        numerator = [1]
        denominator = 1
        for j, (xj, _) in enumerate(points):
            if i == j:
                continue
            product = [0] * (len(numerator) + 1)
            for degree, coefficient in enumerate(numerator):
                product[degree] = (product[degree] - coefficient * xj) % P
                product[degree + 1] = (
                    product[degree + 1] + coefficient
                ) % P
            numerator = product
            denominator = denominator * (xi - xj) % P
        scale = yi * pow(denominator, P - 2, P) % P
        for degree, coefficient in enumerate(numerator):
            result[degree] = (result[degree] + scale * coefficient) % P
    return result


def row_is_degree_lt_k(row: list[int], support: set[int]) -> bool:
    nodes = sorted(support)
    if len(nodes) <= K:
        return True
    polynomial = interpolate(
        [(COORDINATES[j], row[j]) for j in nodes[:K]]
    )
    return all(
        evaluate(polynomial, COORDINATES[j]) == row[j] for j in nodes
    )


def determinant_polynomial(i: int, j: int, k: int) -> list[int]:
    """Collinearity determinant for lifted points (gamma_i, q_i)."""
    out = []
    for degree in range(K):
        qi = POLYNOMIALS[i][degree] if degree < len(POLYNOMIALS[i]) else 0
        qj = POLYNOMIALS[j][degree] if degree < len(POLYNOMIALS[j]) else 0
        qk = POLYNOMIALS[k][degree] if degree < len(POLYNOMIALS[k]) else 0
        out.append(
            ((qk - qi) * (GAMMAS[j] - GAMMAS[i])
             - (qj - qi) * (GAMMAS[k] - GAMMAS[i])) % P
        )
    return out


def main() -> None:
    assert P == w4.P
    assert len(set(COORDINATES)) == N
    assert all(len(poly) <= K for poly in POLYNOMIALS)

    agreements = []
    for gamma, polynomial in zip(GAMMAS, POLYNOMIALS, strict=True):
        agreements.append({
            coordinate
            for coordinate, x in enumerate(COORDINATES)
            if evaluate(polynomial, x)
            == (RECEIVED_U0[coordinate]
                + gamma * RECEIVED_U1[coordinate]) % P
        })

    pairs = list(itertools.combinations(range(5), 2))
    triples = list(itertools.combinations(range(5), 3))
    agreement_counts = [len(support) for support in agreements]
    pair_counts = {
        str(pair): len(agreements[pair[0]] & agreements[pair[1]])
        for pair in pairs
    }
    no_joint = [
        not (
            row_is_degree_lt_k(RECEIVED_U0, support)
            and row_is_degree_lt_k(RECEIVED_U1, support)
        )
        for support in agreements
    ]
    determinant_coefficients = {
        str(triple): determinant_polynomial(*triple) for triple in triples
    }
    collinear_triples = [
        triple
        for triple in triples
        if all(coefficient == 0
               for coefficient in determinant_coefficients[str(triple)])
    ]

    report = {
        "field": P,
        "n": N,
        "k": K,
        "agreement_threshold": T,
        "labels": GAMMAS,
        "agreement_counts": agreement_counts,
        "pair_overlap_counts": pair_counts,
        "no_joint": no_joint,
        "collinear_triples": collinear_triples,
        "all_vertices_rich": all(count >= T for count in agreement_counts),
        "is_five_clique": all(count >= K for count in pair_counts.values()),
        "general_position": not collinear_triples,
        "scope": (
            "exact arbitrary-domain [32,8] RS counterexample; the canonical "
            "roots-of-unity domain remains a separate question"
        ),
    }
    print(json.dumps(report, indent=2, sort_keys=True))

    assert report["all_vertices_rich"]
    assert report["is_five_clique"]
    assert all(no_joint)
    assert report["general_position"]
    print("probe_rate_quarter_five_clique_general_position_counterexample: PASS")


if __name__ == "__main__":
    main()
