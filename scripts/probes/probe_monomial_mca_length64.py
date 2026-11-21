#!/usr/bin/env python3
"""Count all bad challenges for every monomial pair on 64 points at 23 agreements."""

from collections import Counter
from itertools import combinations
from math import gcd


LENGTH = 64
DIMENSION = 4
AGREEMENTS = 23
SECOND_PRIME = 730750818665451459101842416358141509841924915201
SECOND_GENERATOR = 192152681249815148642741928588691886362054863855
EXPECTED = {0: 3496, 1: 516, 2: 48, 4: 16, 5: 8, 32: 4, 64: 8}


def batch_inverse(values, prime):
    """Invert all nonzero residues with one field inversion."""
    products = [1]
    for value in values:
        products.append(products[-1] * (value or 1) % prime)
    inverse = pow(products[-1], -1, prime)
    result = [0] * len(values)
    for i in reversed(range(len(values))):
        if values[i]:
            result[i] = products[i] * inverse % prime
            inverse = inverse * values[i] % prime
    return result


def residual_tables(domain, prime):
    # Partition the ordered sites into seven consecutive blocks of length at most ten.
    # Any 23 sites contain four in one block. Rotating their first site to 1 leaves
    # an interpolating support described by three offsets from 1 through 9.
    blocks = (AGREEMENTS - 1) // (DIMENSION - 1)
    width = (LENGTH + blocks - 1) // blocks
    powers = [[pow(x, a, prime) for x in domain] for a in range(LENGTH)]
    residuals = [[] for _ in powers]
    inverses = [[] for _ in powers]
    for offsets in combinations(range(1, width), DIMENSION - 1):
        support = (0,) + offsets
        lagrange = []
        for i in support:
            numerator = [1] * LENGTH
            denominator = 1
            for j in support:
                if j == i:
                    continue
                denominator = denominator * (domain[i] - domain[j]) % prime
                numerator = [v * (x - domain[j]) % prime for x, v in zip(domain, numerator)]
            inverse = pow(denominator, -1, prime)
            lagrange.append([v * inverse % prime for v in numerator])
        for a, word in enumerate(powers):
            residual = [
                (sum(word[i] * basis[x] for i, basis in zip(support, lagrange)) - word[x]) % prime
                for x in range(LENGTH)
            ]
            residuals[a].append(residual)
            inverses[a].append(batch_inverse(residual, prime))
    return residuals, inverses


def count_pair(first, second, second_inverse, orbit, prime):
    """Use the interpolating supports to count bad scalars in either row order."""
    zero_first = False
    zero_second = False
    nonzero_orbits = set()
    for values, other, inverse in zip(first, second, second_inverse):
        joint = sum(u == 0 and v == 0 for u, v in zip(values, other))
        needed = max(1, AGREEMENTS - joint)
        first_only = sum(u == 0 and v != 0 for u, v in zip(values, other))
        second_only = sum(u != 0 and v == 0 for u, v in zip(values, other))
        zero_first |= first_only >= needed
        zero_second |= second_only >= needed
        if LENGTH - joint - first_only - second_only < needed:
            continue
        ratios = Counter((-u * inv) % prime for u, inv in zip(values, inverse) if u and inv)
        nonzero_orbits.update(pow(c, orbit, prime) for c, m in ratios.items() if m >= needed)
    common = orbit * len(nonzero_orbits)
    return common + zero_first, common + zero_second


def census(prime, root):
    if pow(root, LENGTH, prime) != 1 or pow(root, LENGTH // 2, prime) == 1:
        raise ValueError("The supplied root has the wrong order")
    domain = [pow(root, i, prime) for i in range(LENGTH)]
    residuals, inverses = residual_tables(domain, prime)
    counts = Counter()
    maximizing = []
    maximum = -1
    for a in range(LENGTH):
        for b in range(a, LENGTH):
            orbit = LENGTH // gcd(LENGTH, a - b)
            totals = count_pair(residuals[a], residuals[b], inverses[b], orbit, prime)
            ordered = [(a, b, totals[0])]
            if a != b:
                ordered.append((b, a, totals[1]))
            for left, right, total in ordered:
                counts[total] += 1
                if total > maximum:
                    maximum = total
                    maximizing.clear()
                if total == maximum:
                    maximizing.append((left, right))
    if counts != EXPECTED:
        raise ArithmeticError(f"Unexpected census for {prime}: {counts}")
    print(f"p={prime} maximum={maximum} pairs={sorted(maximizing)}")
    print(f"counts={sorted(counts.items())}")


if __name__ == "__main__":
    census(257, 81)
    census(SECOND_PRIME, pow(SECOND_GENERATOR, 2**30 // LENGTH, SECOND_PRIME))
