#!/usr/bin/env python3
"""Exact finite fourth-moment bounds for any received word at budget twice the length."""

from fractions import Fraction
from itertools import combinations
from math import comb, isqrt
from random import Random


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def bounds(n, t, s, minimum_intersection=None):
    """Lower and upper bounds for tr((D²-I)²) if 2n+1 supports exist."""
    m, a = 2 * n + 1, t - s
    require(0 <= s < t <= n and n * s >= t * t, "outside the non-strict Johnson case")
    lower_intersection = max(0, 2 * t - n)
    if minimum_intersection is not None:
        lower_intersection = max(lower_intersection, minimum_intersection)
    require(lower_intersection <= s, "empty intersection interval")
    kappa = Fraction(s - lower_intersection, a)
    limit = 1 + Fraction(m * (n * s - t * t), n * a)
    lower = m * (1 - kappa**2) if kappa <= 1 else 0
    upper = 2 * limit * (limit - 1) * (limit + 1)**2
    return kappa, limit, lower, upper


def refined_bounds(n, t, s):
    """Fourth trace after bounding the entrywise fourth powers with a cubic trace."""
    cap, limit, _, upper = bounds(n, t, s)
    require(cap < 1, "the refinement requires a strict entry cap")
    m = 2*n + 1
    cubic = (limit - 1) * (limit + 1)**2
    radicand = cubic * (m - 1 + limit)
    root = isqrt(radicand.numerator // radicand.denominator) + 1
    cubic_absolute = limit * (limit**2 - 1) + cubic + root
    negative_squared = (root + limit**2 - 1) / 2
    entry_fourth = (cap * cubic_absolute + 2*cap**2 * negative_squared) / (1 - cap**2)
    return m - entry_fourth, upper


def check_cubic_weights(matrix):
    """Check the normalized cubic entry witness directly, including unequal row masses."""
    m = len(matrix)
    squared = [[sum(a*b for a,b in zip(row, column, strict=True))
                for column in matrix] for row in matrix]
    cubed = [[sum(a*b for a,b in zip(row, column, strict=True))
              for column in matrix] for row in squared]
    cap = max(map(max, matrix))
    rows = [squared[i][i] for i in range(m)]
    weights = [[matrix[i][j]**3 / max(1, rows[i], rows[j]) for j in range(m)]
               for i in range(m)]
    require(all(sum(row) <= cap for row in weights), "weighted row mass")
    witness = sum(weights[i][j]*(cubed[i][j] - matrix[i][j]) for i in range(m) for j in range(m))
    fourth = sum(sum(x**4 for x in row) for row in matrix)
    require((1-cap**2)*fourth <= witness + 2*cap**2*sum(max(0,1-r) for r in rows),
            "normalized cubic lower bound")


def exact_matrix_control():
    """The triples through the origin-lines in F₂⁴ give more than twice 15 blocks."""
    n, t, s = 15, 3, 1
    m, a = 2 * n + 1, t - s
    triples = sorted({tuple(sorted((x, y, x ^ y))) for x, y in combinations(range(1, 16), 2)})
    require(len(triples) == 35, "wrong number of triples")
    for seed in (2, 7, 19):
        sets = [set(row) for row in Random(seed).sample(triples, m)]
        numerators = [[0 if i == j else s - len(x & y) for j, y in enumerate(sets)]
                      for i, x in enumerate(sets)]
        require(all(x >= 0 for row in numerators for x in row), "negative deficit")
        square = [[sum(x * y for x, y in zip(row_i, row_j)) for row_j in numerators]
                  for row_i in numerators]
        second = Fraction(sum(square[i][i] for i in range(m)), a**2)
        q = Fraction(sum((square[i][j] - (a**2 if i == j else 0))**2
                         for i in range(m) for j in range(m)), a**4)
        _, _, lower, upper = bounds(n, t, s)
        require(second >= m and lower <= q <= upper, "actual matrix violates moment bounds")
        check_cubic_weights([[Fraction(x, a) for x in row] for row in numerators])

    # A separate elementary packing check verifies a strictly post-Johnson toy exclusion.
    _, _, lower, upper = bounds(17, 4, 1)
    require(lower > upper and comb(17, 2) // comb(4, 2) < 35, "small exclusion")
    print("Checked the actual fourth traces of three 31-block systems and a 17-site exclusion.")


def main():
    exact_matrix_control()
    n = 2**30
    for den, last_safe, first_lower in [
            (2, 314_491_712, 314_491_713),
            (8, 694_116_789, 694_116_790),
            (16, 805_306_402, 805_306_403)]:
        s = n // den - 1
        t = n - last_safe
        _, _, lower, upper = bounds(n, t, s)
        require(lower > upper and last_safe + 1 == first_lower, "claimed floor fails")
        _, _, next_lower, next_upper = bounds(n, t - 1, s)
        require(next_lower <= next_upper, "certificate reaches a later error")
        require(all(bounds(n, u, s)[2] > bounds(n, u, s)[3]
                    for u in range(t, isqrt(n * s) + 1)), "unexpected gap in the check")
        print(f"Rate 1/{den}, all centers safe through {last_safe:,} errors at budget 2n. "
              f"The fourth trace is at least {lower.numerator // lower.denominator:,} "
              f"and at most {-(-upper.numerator // upper.denominator):,} if 2n+1 words exist.")

    for den, last_safe in ((2, 314_491_712), (8, 694_116_791), (16, 805_306_403)):
        t, s = n - last_safe, n // den - 1
        lower, upper = refined_bounds(n, t, s)
        next_lower, next_upper = refined_bounds(n, t - 1, s)
        require(lower > upper and next_lower <= next_upper, "refined comparison endpoints")
        print(f"Weighted cubic estimate at rate 1/{den}: {last_safe:,} safe errors, "
              f"fourth trace at least {lower.numerator // lower.denominator:,} "
              f"and at most {-(-upper.numerator // upper.denominator):,} for an oversized list.")

    s, t = n // 4 - 1, n // 2 - 2
    _, _, lower900, upper = bounds(n, t, s, 900)
    _, _, lower901, _ = bounds(n, t, s, 901)
    require(lower900 <= upper < lower901, "quarter near-complement threshold")
    print("Rate 1/4, an over-budget family at 536,870,914 errors has a pair overlapping "
          "on at most 900 selected agreement sites.")


if __name__ == "__main__":
    main()
