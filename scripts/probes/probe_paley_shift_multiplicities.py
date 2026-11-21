#!/usr/bin/env python3
"""Compare character sums with a polynomial determinant and its local ranks over F_p."""

from itertools import combinations
from math import comb, isqrt, prod
from random import Random


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def trim(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def multiply(left, right, p):
    if not left or not right:
        return []
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                result[i + j] += a * b
    return trim([entry % p for entry in result])


def add_signed(left, right, sign, p):
    result = left + [0] * max(0, len(right) - len(left))
    for j, value in enumerate(right):
        result[j] = (result[j] + sign * value) % p
    return trim(result)


def poly_det(matrix, p):
    """Leibniz expansion accumulated by used columns, without polynomial division."""
    width = len(matrix)
    partial = {0: [1]}
    for row in matrix:
        following = {}
        for mask, coefficient in partial.items():
            for j in range(width):
                if mask & (1 << j):
                    continue
                new = mask | (1 << j)
                sign = (-1) ** (mask >> (j + 1)).bit_count()
                term = multiply(coefficient, row[j], p)
                following[new] = add_signed(following.get(new, []), term, sign, p)
        partial = following
    return partial[(1 << width) - 1]


def field_rank(matrix, p):
    rows = [row[:] for row in matrix]
    rank = 0
    for j in range(len(matrix)):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        reciprocal = pow(rows[rank][j], -1, p)
        for i in range(rank + 1, len(rows)):
            scale = rows[i][j] * reciprocal % p
            rows[i] = [(u - scale * v) % p for u, v in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def evaluate(poly, x, p):
    value = 0
    for c in reversed(poly):
        value = (value * x + c) % p
    return value


def translated_coefficients(poly, b, p):
    """Coefficients of poly(b+X), used for a direct local multiplicity check."""
    result = []
    for c in reversed(poly):
        result = multiply(result, [b, 1], p)
        result = add_signed(result, [c], 1, p)
    return result


def jet_polynomials(sites, degree, width, constant, p):
    # Barycentric weights give zero moments through degree |A|-2 and one at |A|-1.
    weights = [pow(prod(u - v for v in sites if v != u), -1, p) for u in sites]
    base = [comb(degree, j) * sum(c * pow(u, degree - j, p)
            for u, c in zip(sites, weights)) % p for j in range(degree + 1)]
    base[0] = (base[0] - constant) % p
    base = trim(base)
    jets = []
    for k in range(2 * width - 1):
        normalizer = pow(comb(degree, k), -1, p)
        jets.append(trim([base[j] * comb(j, k) * normalizer % p
                          for j in range(k, len(base))]))
    return jets


def determinant(jets, width, p):
    return poly_det([jets[i:i + width] for i in range(width)], p)


def check_domain(sites, p, check_defects):
    a = len(sites)
    x, d = a // 2, (p - 1) // 2
    signs = [0 if not i else (1 if pow(i, d, p) == 1 else -1) for i in range(p)]
    rows = [[signs[(b + u) % p] for u in sites] for b in range(p)]
    jets = jet_polynomials(sites, d + a - 2, x, 0, p)
    central = determinant(jets, x, p)
    require(len(central) == x * (d - x) + 1, (p, sites, "central degree"))

    product = [central[-1]]
    for b, row in enumerate(rows):
        total, zero = sum(row), row.count(0)
        for _ in range(total * total // 4):
            product = multiply(product, [-b, 1], p)
        size = (a - zero) // 2
        values = [evaluate(poly, b, p) for poly in jets]
        local = [values[i:i + size] for i in range(size)]
        require(field_rank(local, p) == min(row.count(1), row.count(-1)),
                (p, sites, b, "rank"))
    require(central == product, (p, sites, "central factorization"))

    sums = sorted(sum(row) for row in rows)
    signed_maximum = max(sum(sums[-a:]), -sum(sums[:a]))
    largest_magnitudes = sum(sorted(map(abs, sums), reverse=True)[:a])
    require(signed_maximum <= largest_magnitudes, (p, sites, "lower tail estimate"))
    require((p - a) * largest_magnitudes <= 2 * p * signed_maximum,
            (p, sites, "upper tail estimate"))

    if check_defects:
        for sign in [-1, 1]:
            jets = jet_polynomials(sites, d + a - 1, x, sign, p)
            for size in range(1, x + 1):
                poly = determinant(jets, size, p)
                require(len(poly) == size * (d + 1 - size) + 1, "defect degree")
                for b, row in enumerate(rows):
                    errors, zero = row.count(-sign), row.count(0)
                    bound = max(0, size - errors) * max(0, a + 1 - zero - size - errors)
                    if bound:
                        translated = translated_coefficients(poly, b, p)
                        require(all(c == 0 for c in translated[:bound]),
                                (p, sites, sign, size, b, "defect order"))
    return p


def main():
    rng = Random(20261121)
    counts = [0, 0]
    for p in (5, 7, 11, 13, 17, 23, 31, 47, 97):
        if p <= 13:
            domains = [sites for a in range(2, min((p + 1) // 2, 4) + 1)
                       for sites in combinations(range(p), a)]
        else:
            domains = [rng.sample(range(p), a) for a in (5, 6, 7, 8, 9)]
        for sites in domains:
            counts[1] += check_domain(sites, p, p > 13)
            counts[0] += 1
    print(f"{counts[0]} full polynomial factorizations; {counts[1]} exact shift ranks")

    p, a, b, size = 65537, 256, 256, 64
    numerator = b*b*(a - 2*size)**2 + 4*b*size*((p - 1)//2 + 1 - size)
    print(f"p={p}, |A|=|B|=256: |S| + zeros <= {isqrt(numerator)} of {a*b}")


if __name__ == "__main__":
    main()
