#!/usr/bin/env python3
"""Search proper weight-three syndrome lines for punctured RS[9,4].

The no-eight, source-core-seven residual punctures to nine coordinates.  A
candidate closing lemma would bound by twelve the scalars ``gamma`` for which

    base + gamma * direction

has a representative supported on at most three coordinates.  To be useful
for bad-point counting, the representative must also be proper: ``direction``
must not lie in the span of its support columns.

This probe constructs the exact incidence table for the five-dimensional
Vandermonde syndrome columns over F_17.  The domain is a nine-element subset
of the order-sixteen multiplicative group, matching a possible complement of
a seven-coordinate source core in the production n=16 instance.  It then
samples affine lines in vectorized batches.  Any score above twelve is emitted
with exact support and coefficient witnesses and rechecked independently.
"""

import argparse
from itertools import combinations, product

import numpy as np


P = 17
N = 9
K = 4
R = N - K
E = 3


def encode(points):
    """Encode rows of finite-field vectors as base-p integers."""
    points = np.asarray(points, dtype=np.int64)
    powers = np.asarray([P**j for j in range(points.shape[-1])], dtype=np.int64)
    return points @ powers


def decode(index):
    point = []
    for _ in range(R):
        point.append(index % P)
        index //= P
    return tuple(point)


def setup(domain_indices):
    # Three generates F_17^*, so these are distinct points of the production
    # order-sixteen domain.
    full_domain = [pow(3, i, P) for i in range(P - 1)]
    domain = [full_domain[i] for i in domain_indices]
    columns = np.asarray(
        [[pow(x, j, P) for j in range(R)] for x in domain], dtype=np.int64
    )
    supports = list(combinations(range(N), E))

    size = P**R
    low = np.zeros(size, dtype=np.uint64)
    high = np.zeros(size, dtype=np.uint64)
    coefficients = np.asarray(list(product(range(P), repeat=E)), dtype=np.int64)
    for support_index, support in enumerate(supports):
        points = coefficients @ columns[list(support)] % P
        indices = encode(points)
        # The three Vandermonde columns are independent, so the index list has
        # no repetitions and ordinary indexed assignment is exact here.
        assert len(set(map(int, indices))) == P**E
        if support_index < 64:
            low[indices] |= np.uint64(1) << np.uint64(support_index)
        else:
            high[indices] |= np.uint64(1) << np.uint64(support_index - 64)
    return domain, columns, supports, low, high


def bit_index(low, high):
    if low:
        return (low & -low).bit_length() - 1
    return 64 + (high & -high).bit_length() - 1


def solve_support(point, support, columns):
    """Solve point = sum coeff_i * column_i by exact elimination."""
    matrix = np.concatenate(
        [columns[list(support)].T.copy() % P, np.asarray(point)[:, None] % P],
        axis=1,
    )
    row = 0
    pivots = []
    for col in range(E):
        choices = np.flatnonzero(matrix[row:, col])
        if len(choices) == 0:
            continue
        pivot = row + int(choices[0])
        matrix[[row, pivot]] = matrix[[pivot, row]]
        matrix[row] = matrix[row] * pow(int(matrix[row, col]), P - 2, P) % P
        for other in range(R):
            if other != row and matrix[other, col]:
                matrix[other] = (
                    matrix[other] - matrix[other, col] * matrix[row]
                ) % P
        pivots.append(col)
        row += 1
    assert pivots == list(range(E))
    assert not np.any(matrix[row:, :E])
    assert not np.any(matrix[row:, E])
    return tuple(int(matrix[i, E]) for i in range(E))


def nullspace(matrix):
    """Return an exact row basis for the right nullspace over F_p."""
    matrix = np.asarray(matrix, dtype=np.int64).copy() % P
    rows, cols = matrix.shape
    pivots = []
    row = 0
    for col in range(cols):
        choices = np.flatnonzero(matrix[row:, col])
        if len(choices) == 0:
            continue
        pivot = row + int(choices[0])
        matrix[[row, pivot]] = matrix[[pivot, row]]
        matrix[row] = matrix[row] * pow(int(matrix[row, col]), P - 2, P) % P
        for other in range(rows):
            if other != row and matrix[other, col]:
                matrix[other] = (
                    matrix[other] - matrix[other, col] * matrix[row]
                ) % P
        pivots.append(col)
        row += 1
        if row == rows:
            break
    free = [col for col in range(cols) if col not in pivots]
    basis = []
    for free_col in free:
        vector = np.zeros(cols, dtype=np.int64)
        vector[free_col] = 1
        for pivot_row, pivot_col in enumerate(pivots):
            vector[pivot_col] = -matrix[pivot_row, free_col] % P
        basis.append(tuple(map(int, vector)))
    return basis


def score_batch(bases, directions, low, high):
    batch = len(bases)
    gammas = np.arange(P, dtype=np.int64)
    points = (bases[:, None, :] + gammas[None, :, None] * directions[:, None, :]) % P
    point_indices = encode(points.reshape(-1, R)).reshape(batch, P)
    direction_indices = encode(directions)
    joint_low = low[direction_indices, None]
    joint_high = high[direction_indices, None]
    proper = ((low[point_indices] & ~joint_low) != 0) | (
        (high[point_indices] & ~joint_high) != 0
    )
    return proper.sum(axis=1), proper


def inverse(value):
    assert value % P
    return pow(int(value), P - 2, P)


def interpolate_degree_lt_four(values, domain):
    """Interpolate and verify a degree-below-four word on the nine points."""
    vandermonde = np.asarray(
        [[pow(domain[i], j, P) for j in range(K)] for i in range(N)],
        dtype=np.int64,
    )
    matrix = np.concatenate([vandermonde[:K], np.asarray(values[:K])[:, None]], axis=1)
    for col in range(K):
        pivot = col + int(np.flatnonzero(matrix[col:, col] % P)[0])
        matrix[[col, pivot]] = matrix[[pivot, col]]
        matrix[col] = matrix[col] * inverse(matrix[col, col]) % P
        for row in range(K):
            if row != col and matrix[row, col]:
                matrix[row] = (matrix[row] - matrix[row, col] * matrix[col]) % P
    coeffs = matrix[:, K] % P
    assert np.all(vandermonde @ coeffs % P == np.asarray(values) % P)
    return tuple(map(int, coeffs))


def locator(roots):
    coefficients = [1]
    for root in roots:
        out = [0] * (len(coefficients) + 1)
        for degree, coefficient in enumerate(coefficients):
            out[degree] = (out[degree] - root * coefficient) % P
            out[degree + 1] = (out[degree + 1] + coefficient) % P
        coefficients = out
    assert len(coefficients) == K
    return tuple(coefficients)


def source_root_coupling_audit(witnesses, domain):
    """Test whether this thirteen-point line can satisfy the source-root law.

    The seven unused order-sixteen evaluation points form the source core.  We
    lift the unweighted syndrome certificate through the standard dual-GRS
    column weights.  Changing a lift adds common degree-below-four polynomials
    ``f0 + gamma*f1``.  For every selected gamma, the regular source coupling
    requires the resulting decoded polynomial to equal a nonzero scalar times
    one of the 35 cubic locators supported on the seven source points.

    Enumerating the 560 possibilities at gamma=0 and gamma=1 is exhaustive for
    a simultaneous lift of all thirteen certified points.
    """
    full_domain = [pow(3, i, P) for i in range(P - 1)]
    source = full_domain[N:]
    assert set(domain).isdisjoint(source) and len(source) == 7

    weights = []
    for i, x in enumerate(domain):
        denominator = 1
        for j, y in enumerate(domain):
            if i != j:
                denominator = denominator * (x - y) % P
        weights.append(inverse(denominator))

    errors = {}
    for witness in witnesses:
        error = np.zeros(N, dtype=np.int64)
        for index, coefficient in zip(witness["support"], witness["coefficients"]):
            error[index] = coefficient * inverse(weights[index]) % P
        errors[witness["gamma"]] = error
    assert 0 in errors and 1 in errors
    row0 = errors[0]
    row1 = (errors[1] - errors[0]) % P

    decoded = {}
    for gamma, error in errors.items():
        word = (row0 + gamma * row1 - error) % P
        decoded[gamma] = interpolate_degree_lt_four(word, domain)

    allowed = {}
    metadata = {}
    for gamma, polynomial in decoded.items():
        vectors = []
        for roots in combinations(source, K - 1):
            loc = locator(roots)
            for scalar in range(1, P):
                shift = tuple(
                    (scalar * loc[j] - polynomial[j]) % P for j in range(K)
                )
                vectors.append(shift)
                metadata[(gamma, int(encode(np.asarray([shift]))[0]))] = (
                    roots,
                    scalar,
                )
        assert len(vectors) == 35 * (P - 1)
        encoded = encode(np.asarray(vectors, dtype=np.int64))
        assert len(set(map(int, encoded))) == len(vectors)
        allowed[gamma] = encoded

    shifts0 = np.asarray([decode(int(value))[:K] for value in allowed[0]], dtype=np.int64)
    shifts1 = np.asarray([decode(int(value))[:K] for value in allowed[1]], dtype=np.int64)
    flat0 = np.repeat(shifts0, len(shifts1), axis=0)
    flat1 = np.tile(shifts1, (len(shifts0), 1))
    f1 = (flat1 - flat0) % P
    f0 = flat0
    scores = np.zeros(len(f0), dtype=np.int16)
    for gamma in sorted(decoded):
        shifts = (f0 + gamma * f1) % P
        scores += np.isin(encode(shifts), allowed[gamma])
    best_index = int(np.argmax(scores))
    best_score = int(scores[best_index])
    best_f0 = tuple(map(int, f0[best_index]))
    best_f1 = tuple(map(int, f1[best_index]))
    matches = {}
    for gamma in sorted(decoded):
        shift = tuple((best_f0[j] + gamma * best_f1[j]) % P for j in range(K))
        key = int(encode(np.asarray([shift]))[0])
        if key in set(map(int, allowed[gamma])):
            matches[gamma] = metadata[(gamma, key)]
    result = {
        "source_core": tuple(source),
        "dual_weights": tuple(weights),
        "decoded_polynomials": decoded,
        "candidate_lifts_checked": len(scores),
        "best_count_including_gamma_0_1": best_score,
        "best_f0": best_f0,
        "best_f1": best_f1,
        "best_root_scalar_matches": matches,
        "all_thirteen_source_coupled": best_score == len(witnesses),
    }
    print({"source_root_coupling_audit": result}, flush=True)
    return result


def certificate(base, direction, columns, supports, low, high):
    direction_index = int(encode(np.asarray([direction]))[0])
    joint_low = int(low[direction_index])
    joint_high = int(high[direction_index])
    witnesses = []
    for gamma in range(P):
        point = tuple((base[j] + gamma * direction[j]) % P for j in range(R))
        point_index = int(encode(np.asarray([point]))[0])
        proper_low = int(low[point_index]) & ~joint_low
        proper_high = int(high[point_index]) & ~joint_high
        if not proper_low and not proper_high:
            continue
        support_index = bit_index(proper_low, proper_high)
        support = supports[support_index]
        coeffs = solve_support(point, support, columns)
        annihilators = nullspace(columns[list(support)])
        annihilator = next(
            h
            for h in annihilators
            if sum(h[j] * direction[j] for j in range(R)) % P != 0
        )
        reconstructed = tuple(
            sum(coeffs[a] * int(columns[support[a], j]) for a in range(E)) % P
            for j in range(R)
        )
        assert reconstructed == point
        witnesses.append(
            {
                "gamma": gamma,
                "point": point,
                "support": support,
                "coefficients": coeffs,
                "annihilator": annihilator,
            }
        )
    return witnesses


def run(samples, batch_size, seed, domain_indices):
    domain, columns, supports, low, high = setup(domain_indices)
    rng = np.random.default_rng(seed)
    best_score = -1
    best = None
    histogram = np.zeros(P + 1, dtype=np.int64)

    remaining = samples
    while remaining:
        batch = min(batch_size, remaining)
        bases = rng.integers(P, size=(batch, R), dtype=np.int64)
        directions = rng.integers(P, size=(batch, R), dtype=np.int64)
        nonzero = np.any(directions != 0, axis=1)
        if not np.all(nonzero):
            directions[~nonzero, 0] = 1
        scores, _ = score_batch(bases, directions, low, high)
        histogram += np.bincount(scores, minlength=P + 1)
        local = int(np.argmax(scores))
        score = int(scores[local])
        if score > best_score:
            best_score = score
            best = (tuple(map(int, bases[local])), tuple(map(int, directions[local])))
            print(
                {
                    "sample": samples - remaining + local,
                    "new_best": best_score,
                    "base": best[0],
                    "direction": best[1],
                },
                flush=True,
            )
        remaining -= batch

    base, direction = best
    witnesses = certificate(base, direction, columns, supports, low, high)
    assert len(witnesses) == best_score
    coupling = source_root_coupling_audit(witnesses, domain) if best_score > 12 else None
    result = {
        "p": P,
        "n": N,
        "k": K,
        "domain_indices": tuple(domain_indices),
        "domain": tuple(domain),
        "samples": samples,
        "best_score": best_score,
        "base": base,
        "direction": direction,
        "witnesses": witnesses,
        "source_root_coupling": coupling,
        "histogram": {i: int(n) for i, n in enumerate(histogram) if n},
    }
    print(result, flush=True)
    if best_score > 12:
        print("COUNTEREXAMPLE_TO_BARE_TWELVE_BOUND", flush=True)
        return False
    print("NO_COUNTEREXAMPLE_FOUND", flush=True)
    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=1_000_000)
    parser.add_argument("--batch-size", type=int, default=50_000)
    parser.add_argument("--seed", type=int, default=20260710)
    parser.add_argument(
        "--domain-indices",
        type=int,
        nargs=N,
        default=tuple(range(N)),
        help="nine distinct exponent indices in the order-sixteen F_17 domain",
    )
    args = parser.parse_args()
    raise SystemExit(
        0
        if run(args.samples, args.batch_size, args.seed, args.domain_indices)
        else 1
    )
