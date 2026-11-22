#!/usr/bin/env python3
"""Find the largest exceptional split prime for admissible mu_128 three-ratio comparisons.

NumPy batches exact fixed-width integer interval operations. All table entries,
exceptional norms and divisibility checks use unbounded Python integers.
"""
from itertools import combinations_with_replacement
from math import gcd, isqrt

import numpy as np

from probe_mu128_charge_heights import DEGREE, ORDER, SCALE, absolute_norm, comparison, twice_cosine

CHORD_BITS = 16
CHORD_SCALE = 1 << CHORD_BITS
LOG_UNITS = 256
EXCEPTIONAL_PRIME = 105018080988161859083316683155074219521
EMBEDDINGS = np.arange(1, DEGREE, 2, dtype=np.int64)
POWERS_OF_TWO = np.array([1 << i for i in range(62)], dtype=np.int64)
# For positive m this is ceil(256*log2(m)). An upper bound of zero on
# a magnitude permits every finite logarithmic upper bound.
LOG_MANTISSA = np.array(
    [-(1 << 20)] + [(m**LOG_UNITS - 1).bit_length() for m in range(1, 2049)],
    dtype=np.int64,
)


def log_upper(values):
    """Upper bound 256*log2(values) by upward rounding to an 11-bit mantissa."""
    exponents = np.searchsorted(POWERS_OF_TWO, values, side="right") - 1
    shifts = np.maximum(0, exponents - 10)
    mantissas = (values + (1 << shifts) - 1) >> shifts
    return LOG_MANTISSA[mantissas] + LOG_UNITS * shifts


def exact_exclusion(separation, left, right, prime_bits):
    """Any surviving split prime above the floor equals the displayed exceptional prime."""
    prime_floor = 1 << prime_bits
    norm = absolute_norm(comparison(separation, list(map(int, left)), list(map(int, right))))
    if norm == 0:
        return 0, 0, 0
    odd_norm = norm // (norm & -norm)
    root = isqrt(odd_norm)
    assert root * root == odd_norm and root < prime_floor**2
    bits = root.bit_length()
    divisor = 2
    while divisor <= root // prime_floor:
        while root % divisor == 0:
            root //= divisor
        divisor += 1
    if root >= prime_floor:
        # Any prime >= prime_floor dividing root must now equal root.
        split_candidate = root % ORDER == 1 and all(
            pow(a, root - 1, root) == 1
            for a in (2, 3, 5, 7, 11, 13, 17, 19)
        )
        if split_candidate:
            assert root == EXCEPTIONAL_PRIME, (separation, left, right, root)
        return bits, 1, int(split_candidate)
    return bits, 0, 0


def chord_tables():
    """Bound each absolute chord with rational endpoints of denominator 2^16."""
    lower, upper = [], []
    for x in range(ORDER):
        low_cos, high_cos = twice_cosine(ORDER, x)
        lo = (2 * SCALE - high_cos) * CHORD_SCALE**2 // SCALE
        hi = ((2 * SCALE - low_cos) * CHORD_SCALE**2 + SCALE - 1) // SCALE
        lower.append(isqrt(max(0, lo)))
        upper.append(isqrt(hi) + 1)
    indices = np.arange(ORDER, dtype=np.int64)[:, None] * EMBEDDINGS % ORDER
    return np.array(lower, dtype=np.int64)[indices], np.array(upper, dtype=np.int64)[indices]


def coordinate_bounds(rows, separation):
    """Enclose the numerator and denominator, record their relative signs and common powers of two."""
    lower, upper = chord_tables()
    indices = np.arange(ORDER, dtype=np.int64)[:, None]
    # A ratio has phase exp(-pi*i*j*d/128) times a real number. Its sign
    # uses the two sine factors at j*x/128 and j*(x-d)/128.
    negative = (
        (indices * EMBEDDINGS // ORDER - (indices - separation) * EMBEDDINGS // ORDER) % 2
    ).astype(bool)
    ramification = np.array([gcd(x, ORDER) for x in range(ORDER)], dtype=np.int32)
    powers = np.stack((
        ramification[rows].sum(axis=1),
        ramification[(rows - separation) % ORDER].sum(axis=1),
    ), axis=1)
    bounds = np.empty((len(rows), len(EMBEDDINGS), 4), dtype=np.int32)
    signs = np.empty((len(rows), len(EMBEDDINGS)), dtype=bool)
    heights = np.empty(len(rows), dtype=np.int64)
    for start in range(0, len(rows), 1024):
        batch = slice(start, start + 1024)
        x = rows[batch]
        y = (x - separation) % ORDER

        def product_bounds(sites):
            # Three chords < 2+2^-14 give raw products < 2^52.
            lo = np.prod(lower[sites], axis=1) // CHORD_SCALE**2
            hi = (np.prod(upper[sites], axis=1) + CHORD_SCALE**2 - 1) // CHORD_SCALE**2
            return lo, hi

        a_lo, a_hi = product_bounds(x)
        b_lo, b_hi = product_bounds(y)
        bounds[batch] = np.stack((a_lo, a_hi, b_lo, b_hi), axis=2)
        signs[batch] = negative[x[:, 0]] ^ negative[x[:, 1]] ^ negative[x[:, 2]]
        common = powers[batch].min(axis=1)
        heights[batch] = log_upper(a_hi**2 + b_hi**2).sum(axis=1) - LOG_UNITS * (
            2 * CHORD_BITS * len(EMBEDDINGS) + common
        )
    return heights, bounds, signs, powers


def check_row(separation, prime_bits):
    log_square_limit = 2 * prime_bits * LOG_UNITS
    sites = [x for x in range(1, ORDER) if x != separation]
    rows = np.array(
        [t for t in combinations_with_replacement(sites, 3) if t[0] != t[2]], dtype=np.int16
    )
    heights, bounds, signs, powers = coordinate_bounds(rows, separation)
    order = np.argsort(heights)
    rows, heights, bounds, signs, powers = (a[order] for a in (rows, heights, bounds, signs, powers))
    first = np.searchsorted(heights, log_square_limit - heights)
    height_pairs = disjoint_pairs = exact_pairs = remaining_cores = largest_bits = witnesses = 0

    for j in np.flatnonzero(2 * heights >= log_square_limit):
        if first[j] >= j:
            continue
        candidates = np.arange(first[j], j)
        height_pairs += len(candidates)
        # A common site cancels, reducing to the independent two-ratio theorem.
        for x in rows[j]:
            candidates = candidates[np.all(rows[candidates] != x, axis=1)]
        disjoint_pairs += len(candidates)

        for start in range(0, len(candidates), 1536):
            k = candidates[start : start + 1536]
            left, right = bounds[k].astype(np.int64), bounds[j].astype(np.int64)
            a_hi = left[:, :, 1] * right[:, 3]
            b_hi = right[:, 1] * left[:, :, 3]
            a_lo = left[:, :, 0] * right[:, 2]
            b_lo = right[:, 0] * left[:, :, 2]
            # These products are < 2^40. The two crossed terms have a common
            # complex phase up to sign, so subtraction uses real intervals.
            hi = np.where(signs[k] == signs[j], np.maximum(a_hi - b_lo, b_hi - a_lo), a_hi + b_hi)
            common = np.minimum(powers[k, 0] + powers[j, 1], powers[k, 1] + powers[j, 0])
            norm_log = 2 * (log_upper(hi).sum(axis=1) - LOG_UNITS * 2 * CHORD_BITS * len(EMBEDDINGS))
            odd_log = norm_log - LOG_UNITS * common
            for i in k[odd_log >= log_square_limit]:
                bits, needs_core, possible = exact_exclusion(separation, rows[i], rows[j], prime_bits)
                exact_pairs += 1
                largest_bits = max(largest_bits, bits)
                remaining_cores += needs_core
                witnesses += possible
    return len(rows), height_pairs, disjoint_pairs, exact_pairs, largest_bits, remaining_cores, witnesses


if __name__ == "__main__":
    expected = {
        1: (341250, 2892583, 1828647, 47, 136, 47, 0),
        2: (341250, 2149586, 1333614, 32, 138, 32, 0),
        4: (341250, 690705, 425295, 4, 134, 2, 0),
        8: (341250, 88200, 55252, 0, 0, 0, 0),
        16: (341250, 1, 1, 0, 0, 0, 0),
        32: (341250, 5584, 5536, 48, 86, 0, 0),
    }
    sharp = {
        1: (341250, 4547897, 3130483, 90, 136, 86, 2),
        2: (341250, 3584159, 2393547, 63, 138, 63, 0),
        4: (341250, 1563264, 958772, 8, 134, 8, 0),
        8: (341250, 155574, 98060, 0, 0, 0, 0),
        16: (341250, 193, 177, 0, 0, 0, 0),
        32: (341250, 6096, 6048, 48, 86, 0, 0),
    }
    for bits, counts in ((128, expected), (126, sharp)):
        for d, reference in counts.items():
            result = check_row(d, bits)
            assert result == reference, (bits, d, result)
            print(f"p >= 2^{bits}, d={d:2}: records, height pairs, disjoint pairs, exact norms, "
                  f"largest odd square-root bits, final core tests, exceptional-prime candidates = {result}", flush=True)
