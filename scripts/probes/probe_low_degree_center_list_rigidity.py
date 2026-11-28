#!/usr/bin/env python3
"""Check exact full-size consequences and small locator fibers at both named primes."""

from collections import defaultdict
from itertools import combinations
from math import comb, prod


PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)
N = 1 << 30
NAMED_ROWS = (
    (2, 315_391_701, 87_261_483, 3, 3),
    (2, 314_991_701, 87_661_483, 3, 3),
    (2, 314_491_700, 88_161_484, 3, 3),
    (2, 314_491_713, 88_161_471, 3, 3),
    (4, 536_870_914, 134_217_726, 3, 5),
    (4, 536_871_005, 134_217_635, 3, 5),
    (4, 536_870_915, 134_217_725, 3, 5),
    (4, 536_870_920, 134_217_720, 3, 5),
    (4, 536_870_932, 134_217_708, 3, 5),
    (4, 536_870_934, 134_217_706, 3, 5),
    (4, 539_018_396, 132_070_244, 3, 5),
    (4, 538_870_915, 132_217_725, 3, 5),
    (4, 538_320_915, 132_767_725, 3, 5),
    (4, 537_870_915, 133_217_725, 3, 5),
    (4, 543_870_915, 127_217_725, 3, 5),
    (8, 694_116_763, 111_189_605, 3, 3),
    (8, 695_116_764, 110_189_604, 3, 3),
    (8, 705_616_764, 99_689_604, 3, 3),
    (8, 704_116_764, 101_189_604, 3, 3),
    (8, 697_616_764, 107_689_604, 3, 3),
    (8, 694_116_764, 111_189_604, 3, 3),
    (8, 694_116_790, 111_189_578, 3, 3),
    (8, 694_116_792, 111_189_576, 3, 3),
    (16, 805_306_371, 67_108_861, 1, 1),
    (16, 806_056_372, 66_358_860, 1, 1),
    (16, 816_806_372, 55_608_860, 1, 1),
    (16, 805_306_403, 67_108_829, 1, 1),
    (16, 805_306_404, 67_108_828, 1, 1),
    (16, 805_531_369, 66_883_863, 1, 1),
    (16, 810_406_369, 62_008_863, 1, 1),
    (16, 818_306_369, 54_108_863, 1, 1),
)


def primitive_root_of_order(n, p):
    for base in range(2, 1000):
        g = pow(base, (p - 1) // n, p)
        if pow(g, n // 2, p) == p - 1 and pow(g, n, p) == 1:
            return g
    raise ArithmeticError("No primitive root found in the search interval")


def class_maximum(n, blocks, weight):
    full, remainder = divmod(weight, n // blocks)
    return comb(blocks - bool(remainder), full)


def largest_residue_fiber(labels, weight):
    fibers = defaultdict(list)
    for selection in combinations(labels, weight):
        fibers[sum(selection) % 8].append(selection)
    return max(fibers.values(), key=len)


def split_coset(n, residue, size, count):
    """Disjoint dyadic cosets partition one class, with exactly count sites marked."""
    pieces = []
    while 0 < count < size:
        step = n // size
        size //= 2
        if count >= size:
            pieces.append((residue, size, True))
            count -= size
            residue += step
        else:
            pieces.append((residue + step, size, False))
    pieces.append((residue, size, count == size))
    return pieces


def check_named_witness(n, p, g, k, t, blocks):
    """Evaluate sparse factorizations at every atom of the full-size witness partition."""
    q = n // blocks
    full, remainder = divmod(t, q)
    pure = range(blocks - bool(remainder))
    partial = split_coset(n, blocks - 1, q, remainder) if remainder else []
    atoms = [(residue, q, False) for residue in pure] + partial
    assert sum(size for _, size, _ in atoms) == n
    assert sum(size for _, size, marked in partial if marked) == remainder
    for (a, u, _), (b, v, _) in combinations(atoms, 2):
        assert (a - b) % min(n // u, n // v)
    signatures = set()
    marked = [(r, size) for r, size, used in partial if used]
    if blocks == 8:
        selections = largest_residue_fiber(pure, full)
        shift = t - k - q + 1
        assert 1 <= shift <= q
        constants = {prod(-pow(g, r * q, p) for r in sel) % p for sel in selections}
        assert len(constants) == 1
    else:
        selections = list(combinations(pure, full))
        shift = 0
    for selection in selections:
        factors = marked + [(r, q) for r in selection]
        assert sum(size for _, size in factors) == t
        signature = []
        agreements = 0
        for r, size, included in atoms:
            x = pow(g, r, p)
            residual = 1
            for root, degree in factors:
                residual = residual * (pow(x, degree, p) - pow(g, root * degree, p)) % p
            expected = included or (size == q and r in selection)
            assert (residual == 0) == expected
            signature.append(residual == 0)
            if residual == 0:
                agreements += size
        assert agreements == t
        signatures.add(tuple(signature))
    # The equal constants in the shifted case give divisibility by X^q as well.
    assert t - q - shift < k and len(signatures) == len(selections)
    return len(signatures)


def exchange_class(mask, blocks):
    """Partial blocks stay fixed; only the labels of full blocks can change."""
    partial = []
    full = 0
    for block in blocks:
        occupied = mask & block
        if occupied == block:
            full += 1
            occupied = 0
        partial.append(occupied)
    return full, tuple(partial)


def check_subsets(n, p):
    g = primitive_root_of_order(n, p)
    points = [pow(g, j, p) for j in range(n)]
    quarter_classes = [sum(1 << j for j in range(i, n, 4)) for i in range(4)]
    eighth_classes = [sum(1 << j for j in range(i, n, 8)) for i in range(8)]
    max_depth = n // 4 - 1
    # Below-leading coefficients of the monic locator, padded with zero.
    coefficients = [(0,) * max_depth] * (1 << n)
    low = [(1,) + (0,) * (max_depth - 1)] * (1 << n)
    signatures = {depth: {} for depth in range(n // 8, max_depth + 1)}
    reverse = {depth: {} for depth in signatures}
    # Each length-n/8 interval containing zero tests the two-sided bound.
    intervals = [tuple(range(-a, n // 8 - a)) for a in range(n // 8)]
    interval_classes = [{} for _ in intervals]
    interval_powers = [
        [tuple(pow(x, u, p) for u in span) for x in points] for span in intervals
    ]
    interval_values = [[(0,) * len(span)] * (1 << n) for span in intervals]
    for mask in range(1 << n):
        weight = mask.bit_count()
        if mask:
            bit = mask & -mask
            j = bit.bit_length() - 1
            prev = mask ^ bit
            old = (1,) + coefficients[prev]
            coefficients[mask] = tuple(
                (old[i + 1] - points[j] * old[i]) % p for i in range(max_depth)
            )
            last = low[prev]
            low[mask] = tuple(
                ((last[i - 1] if i else 0) - points[j] * last[i]) % p for i in range(max_depth)
            )
            for index, powers in enumerate(interval_powers):
                interval_values[index][mask] = tuple(
                    (a + b) % p for a, b in zip(interval_values[index][prev], powers[j])
                )
        predicted = exchange_class(mask, quarter_classes)
        for depth, bucket in signatures.items():
            key = weight, coefficients[mask][:depth]
            prior, size = bucket.get(key, (predicted, 0))
            assert predicted == prior
            bucket[key] = predicted, size + 1
            assert reverse[depth].setdefault((weight, predicted), key) == key
        predicted_eighth = exchange_class(mask, eighth_classes)
        for values, classes in zip(interval_values, interval_classes):
            key = weight, values[mask]
            assert classes.setdefault(key, predicted_eighth) == predicted_eighth

    for bucket in signatures.values():
        maxima = [0] * (n + 1)
        for (weight, _), (_, size) in bucket.items():
            maxima[weight] = max(maxima[weight], size)
        assert maxima == [class_maximum(n, 4, w) for w in range(n + 1)]
    # Exact degree-t monic numerator lists with denominator X^s. Matching the
    # low s coefficients makes differences divisible by X^s. Matching the first
    # depth-s high coefficients gives the degree bound after the division.
    for depth in signatures:
        maxima = [class_maximum(n, 4, w) for w in range(n + 1)]
        for shift in range(1, depth + 1):
            counts = defaultdict(int)
            for mask, high in enumerate(coefficients):
                key = mask.bit_count(), high[:depth - shift], low[mask][:shift]
                counts[key] += 1
            for (weight, _, _), size in counts.items():
                maxima[weight] = max(maxima[weight], size)
        for weight in range(depth + 1, n):
            j, remainder = divmod(weight, n // 8)
            predicted = len(largest_residue_fiber(range(8 - bool(remainder)), j))
            assert maxima[weight] == predicted
    print(f"order {n}, {p.bit_length()}-bit field: {1 << n:,} exact subset checks")


def main():
    for p in PRIMES:
        assert (p - 1) % N == 0 and p > (2 * N) ** 4
        g = primitive_root_of_order(N, p)
        # At order >=16 the common norm exponents cancel to this small inequality.
        for r in range(4, 31):
            size = 1 << r
            assert (2 * size) ** 4 < p and size // 16 >= 1
        assert 16**2 < p
        for size in (8, 16):
            check_subsets(size, p)
        for rate, errors, _, sharp, shifted in NAMED_ROWS:
            assert check_named_witness(N, p, g, N // rate, N - errors, 4) == sharp
            assert check_named_witness(N, p, g, N // rate, N - errors, 8) == shifted
        print(f"Compared all named witness supports at length {N:,} over the {p.bit_length()}-bit field.")
    for rate, errors, denominator, sharp, shifted in NAMED_ROWS:
        k = N // rate
        t = N - errors
        assert N // 8 <= t - k < N // 4
        assert t - k - N // 8 == denominator
        assert class_maximum(N, 4, t) == sharp
        j, r = divmod(t, N // 8)
        assert len(largest_residue_fiber(range(8 - bool(r)), j)) == shifted
        assert (t + 1) + (t - k + 1) < N
        print(f"rate 1/{rate}, {errors:,} errors: polynomial cap {sharp}, shifted cap {shifted}")
    endpoints = [(N - (N // d + N // 8), class_maximum(N, 4, N // d + N // 8))
                 for d in (2, 4, 8, 16)]
    assert endpoints == [(402_653_184, 3), (671_088_640, 3),
                         (805_306_368, 4), (872_415_232, 1)]
    for labels, expected in ((8, [1, 1, 4, 7, 10, 7, 4, 1, 1]),
                             (7, [1, 1, 3, 5, 5, 3, 1, 1])):
        for j, cap in enumerate(expected):
            assert len(largest_residue_fiber(range(labels), j)) == cap
            t = j * (N // 8) + (labels == 7)
            assert class_maximum(N, 4, t) <= cap
    print("All restricted polynomial-center endpoints reproduced.")


if __name__ == "__main__":
    main()
