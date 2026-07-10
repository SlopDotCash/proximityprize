#!/usr/bin/env python3
"""Probe the actual source-root-coupled no-eight seven-core geometry.

Fix the full order-sixteen domain in F_17, a seven-coordinate source core D,
and its nine-coordinate complement V.  After subtracting the source decoded
line, the received rows vanish on D.  For an outsider at scalar gamma, a
degree-below-four nonzero residual polynomial p is legal precisely when

    agreements_V(A + gamma R, p) + roots_D(p) >= 9.

The V-agreement count is at least six automatically.  This single test keeps
all regular and long types, including (fresh, roots) = (6,3), (7,2/3),
(8,1/2/3), and (9,0/1/2/3).  It is stronger than bare quotient weight <= 3.

The search samples affine row pairs through two legal outsiders.  Every score
is exact.  New records are also checked for the global core cap: no pair of
degree-below-four row polynomials may jointly agree on more than seven of the
sixteen coordinates.  This is a falsification probe, not a proof of a bound.
"""

import argparse
from itertools import combinations, product

import numpy as np


P = 17
N = 16
K = 4
SOURCE_SIZE = 7
V_SIZE = N - SOURCE_SIZE


def inverse(value):
    assert value % P
    return pow(int(value), P - 2, P)


def matrix_inverse(matrix):
    matrix = np.asarray(matrix, dtype=np.int64) % P
    size = len(matrix)
    augmented = np.concatenate([matrix, np.eye(size, dtype=np.int64)], axis=1)
    for col in range(size):
        choices = np.flatnonzero(augmented[col:, col])
        assert len(choices)
        pivot = col + int(choices[0])
        augmented[[col, pivot]] = augmented[[pivot, col]]
        augmented[col] = augmented[col] * inverse(augmented[col, col]) % P
        for row in range(size):
            if row != col and augmented[row, col]:
                augmented[row] = (
                    augmented[row] - augmented[row, col] * augmented[col]
                ) % P
    return augmented[:, size:]


def setup():
    # Three generates F_17^*.  The split agrees with the bare-syndrome probe.
    domain = np.asarray([pow(3, i, P) for i in range(N)], dtype=np.int64)
    complement = domain[:V_SIZE]
    source = domain[V_SIZE:]
    vandermonde = np.asarray(
        [[pow(int(x), j, P) for j in range(K)] for x in domain],
        dtype=np.int64,
    )
    vand_v = vandermonde[:V_SIZE]
    vand_d = vandermonde[V_SIZE:]

    anchors_v = np.asarray(list(combinations(range(V_SIZE), K)), dtype=np.int64)
    inverses_v = np.asarray(
        [matrix_inverse(vand_v[anchor]) for anchor in anchors_v], dtype=np.int64
    )
    anchors_full = np.asarray(list(combinations(range(N), K)), dtype=np.int64)
    inverses_full = np.asarray(
        [matrix_inverse(vandermonde[anchor]) for anchor in anchors_full],
        dtype=np.int64,
    )

    coefficients = np.asarray(list(product(range(P), repeat=K)), dtype=np.int64)
    coefficients = coefficients[np.any(coefficients != 0, axis=1)]
    centers_v = coefficients @ vand_v.T % P
    roots_d = np.sum(coefficients @ vand_d.T % P == 0, axis=1)
    centers_by_error_size = {
        error_size: centers_v[roots_d >= error_size]
        for error_size in range(4)
    }
    return {
        "domain": domain,
        "complement": complement,
        "source": source,
        "vandermonde": vandermonde,
        "vand_v": vand_v,
        "vand_d": vand_d,
        "anchors_v": anchors_v,
        "inverses_v": inverses_v,
        "anchors_full": anchors_full,
        "inverses_full": inverses_full,
        "centers_by_error_size": centers_by_error_size,
    }


def sample_bad_words(batch, rng, data):
    # Bias toward the regular stratum while retaining all long types.
    error_sizes = rng.choice(np.asarray([0, 1, 2, 3]), size=batch,
                             p=np.asarray([0.05, 0.10, 0.25, 0.60]))
    words = np.empty((batch, V_SIZE), dtype=np.int64)
    for error_size in range(4):
        rows = np.flatnonzero(error_sizes == error_size)
        if not len(rows):
            continue
        centers = data["centers_by_error_size"][error_size]
        chosen = centers[rng.integers(len(centers), size=len(rows))].copy()
        if error_size:
            supports = np.asarray(list(combinations(range(V_SIZE), error_size)))
            chosen_supports = supports[rng.integers(len(supports), size=len(rows))]
            errors = rng.integers(1, P, size=(len(rows), error_size), dtype=np.int64)
            chosen[np.arange(len(rows))[:, None], chosen_supports] += errors
            chosen %= P
        words[rows] = chosen
    return words


def classify_batch(row0, row1, data):
    batch = len(row0)
    gammas = np.arange(P, dtype=np.int64)
    points = (row0[:, None, :] + gammas[None, :, None] * row1[:, None, :]) % P

    # Interpolate the polynomial through every four-coordinate anchor.  Any
    # polynomial with six V-agreements appears from many of these anchors.
    values = points[:, :, data["anchors_v"]]
    coefficients = np.einsum(
        "bgsi,sij->bgsj", values, data["inverses_v"], optimize=True
    ) % P
    evaluations_v = np.einsum(
        "bgsj,vj->bgsv", coefficients, data["vand_v"], optimize=True
    ) % P
    evaluations_d = np.einsum(
        "bgsj,dj->bgsd", coefficients, data["vand_d"], optimize=True
    ) % P
    fresh = np.sum(evaluations_v == points[:, :, None, :], axis=-1)
    roots = np.sum(evaluations_d == 0, axis=-1)
    nonzero = np.any(coefficients != 0, axis=-1)
    legal = nonzero & (fresh >= 6) & (fresh + roots >= 9)
    outsiders = np.any(legal, axis=-1)

    # Residual zero is a point on the source decoded line.  Its seven source
    # agreements need two additional zeros in V to meet threshold nine.
    source_points = np.sum(points == 0, axis=-1) >= 2
    return points, coefficients, fresh, roots, legal, outsiders, source_points


def global_core_max(row0, row1, data):
    full0 = np.concatenate([row0, np.zeros(SOURCE_SIZE, dtype=np.int64)])
    full1 = np.concatenate([row1, np.zeros(SOURCE_SIZE, dtype=np.int64)])
    anchors = data["anchors_full"]
    coefficients0 = np.einsum(
        "si,sij->sj", full0[anchors], data["inverses_full"], optimize=True
    ) % P
    coefficients1 = np.einsum(
        "si,sij->sj", full1[anchors], data["inverses_full"], optimize=True
    ) % P
    evaluations0 = coefficients0 @ data["vandermonde"].T % P
    evaluations1 = coefficients1 @ data["vandermonde"].T % P
    joint = np.sum(
        (evaluations0 == full0[None, :]) & (evaluations1 == full1[None, :]),
        axis=1,
    )
    index = int(np.argmax(joint))
    return int(joint[index]), tuple(map(int, coefficients0[index])), tuple(
        map(int, coefficients1[index])
    )


def certificate(row0, row1, data):
    arrays = classify_batch(row0[None, :], row1[None, :], data)
    points, coefficients, fresh, roots, legal, outsiders, source_points = arrays
    records = []
    for gamma in range(P):
        legal_indices = np.flatnonzero(legal[0, gamma])
        if len(legal_indices):
            index = int(legal_indices[0])
            records.append(
                {
                    "gamma": gamma,
                    "kind": "outsider",
                    "polynomial": tuple(map(int, coefficients[0, gamma, index])),
                    "fresh": int(fresh[0, gamma, index]),
                    "source_roots": int(roots[0, gamma, index]),
                    "missed": tuple(
                        int(i)
                        for i in np.flatnonzero(
                            coefficients[0, gamma, index] @ data["vand_v"].T % P
                            != points[0, gamma]
                        )
                    ),
                }
            )
        elif source_points[0, gamma]:
            records.append({"gamma": gamma, "kind": "source"})
    return records, int(np.sum(outsiders)), int(np.sum(source_points)), int(
        np.sum(outsiders | source_points)
    )


def run(samples, batch_size, seed):
    data = setup()
    rng = np.random.default_rng(seed)
    best_raw = (-1, None)
    best_core_safe = (-1, None)
    best_residual_shaped = (-1, None)
    remaining = samples
    histogram = np.zeros(P + 1, dtype=np.int64)

    while remaining:
        batch = min(batch_size, remaining)
        endpoint0 = sample_bad_words(batch, rng, data)
        endpoint1 = sample_bad_words(batch, rng, data)
        row0 = endpoint0
        row1 = (endpoint1 - endpoint0) % P
        exact_source = ~np.any((row0 == 0) & (row1 == 0), axis=1)
        _, _, _, _, _, outsiders, source_points = classify_batch(row0, row1, data)
        scores = np.sum(outsiders, axis=1)
        scores[~exact_source] = -1
        source_counts = np.sum(source_points, axis=1)
        source_only = np.sum(source_points & ~outsiders, axis=1)
        coverage = np.sum(outsiders | source_points, axis=1)
        source_loss = np.maximum(0, 2 - source_only)
        residual_scores = scores - source_loss
        residual_scores[(source_counts < 2) | (coverage < P) | ~exact_source] = -1
        histogram += np.bincount(scores[scores >= 0], minlength=P + 1)
        order = np.argsort(scores)[::-1]
        candidates = [
            int(local)
            for local in order
            if scores[local] > best_core_safe[0]
            or residual_scores[local] > best_residual_shaped[0]
            or scores[local] > best_raw[0]
        ]
        for local in candidates:
            score = int(scores[local])
            core = global_core_max(row0[local], row1[local], data)
            source_count = int(source_counts[local])
            covered = int(coverage[local])
            payload = {
                "sample": samples - remaining + int(local),
                "outside": score,
                "outside_after_choosing_two_source_points": int(
                    residual_scores[local]
                ),
                "source_points": source_count,
                "coverage": covered,
                "global_core_max": core[0],
                "row0": tuple(map(int, row0[local])),
                "row1": tuple(map(int, row1[local])),
            }
            if score > best_raw[0]:
                best_raw = (score, payload)
                print({"new_raw_best": payload}, flush=True)
            if core[0] <= 7 and score > best_core_safe[0]:
                best_core_safe = (score, payload)
                print({"new_core_safe_best": payload}, flush=True)
            if core[0] <= 7 and residual_scores[local] > best_residual_shaped[0]:
                best_residual_shaped = (int(residual_scores[local]), payload)
                print({"new_residual_shaped_best": payload}, flush=True)
        remaining -= batch

    payload = best_core_safe[1]
    records = None
    if payload is not None:
        records, outside, source_count, coverage = certificate(
            np.asarray(payload["row0"]), np.asarray(payload["row1"]), data
        )
        assert outside == payload["outside"]
        assert source_count == payload["source_points"]
        assert coverage == payload["coverage"]
    result = {
        "p": P,
        "domain": tuple(map(int, data["domain"])),
        "complement": tuple(map(int, data["complement"])),
        "source_core": tuple(map(int, data["source"])),
        "samples": samples,
        "best_raw": best_raw,
        "best_global_core_at_most_seven": best_core_safe,
        "best_residual_shaped": best_residual_shaped,
        "best_core_safe_certificate": records,
        "histogram": {i: int(n) for i, n in enumerate(histogram) if n},
    }
    print(result, flush=True)
    if best_core_safe[0] >= 13:
        print("SOURCE_COUPLED_THIRTEEN_POINT_CANDIDATE", flush=True)
        return False
    print("NO_SOURCE_COUPLED_THIRTEEN_POINT_CANDIDATE_FOUND", flush=True)
    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=100_000)
    parser.add_argument("--batch-size", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20260710)
    args = parser.parse_args()
    raise SystemExit(0 if run(args.samples, args.batch_size, args.seed) else 1)
