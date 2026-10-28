#!/usr/bin/env python3
"""Independent cross-check for probe_n16_below_ceiling_max.py.

This script deliberately uses different algorithms than the main probe:

* candidate scalars come from 4-point systems solved by a full 3x3 Gaussian
  elimination (the main probe derives candidates from every triple with a 2x2
  Cramer elimination);
* each candidate is audited by direct 16-point agreement with the solved line
  (the main probe groups pair lines and reads witness sets off pair counts);
* the (x^3,x^2) ceiling count is obtained from the closed-form distinct
  three-element subset-sum set (the main probe runs the MCA event and only uses
  the closed form as an internal check).

The asserted integers are identical to the main probe's.  Stdlib only, exact
integer arithmetic, no floats, hard asserts.
"""

from itertools import combinations
from math import isqrt

N8 = 8
N16 = 16
T_CEIL = 3
T_BELOW = 4

FOUR = ((8, 7), (8, 15), (9, 2), (9, 10))
G328_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))

EXPECTED = {
    (8, 17): (16, 9, G328_WINNERS),
    (8, 41): (40, 9, G328_WINNERS),
    (8, 257): (40, 9, G328_WINNERS),
    (16, 17): (17, 17, None),
    (16, 97): (96, 97, ((8, 15), (9, 2))),
    (16, 113): (112, 97, ((8, 7), (9, 10))),
    (16, 241): (240, 97, ((8, 15), (9, 2))),
    (16, 257): (224, 97, ((8, 15), (9, 2))),
    (16, 353): (272, 81, FOUR),
    (16, 449): (336, 97, ((8, 15), (9, 2))),
    (16, 1201): (464, 97, FOUR),
    (16, 1217): (448, 97, ((8, 15), (9, 2))),
    (16, 12289): (464, 97, FOUR),
    (16, 19489): (464, 97, FOUR),
    (16, 65537): (464, 97, FOUR),
}


def order_element(p, n):
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def solve3(matrix, rhs, p):
    """Solve a 3x3 system by Gauss-Jordan; return None if singular."""
    rows = [list(matrix[i]) + [rhs[i] % p] for i in range(3)]
    for col in range(3):
        pivot = None
        for row in range(col, 3):
            if rows[row][col] % p:
                pivot = row
                break
        if pivot is None:
            return None
        rows[col], rows[pivot] = rows[pivot], rows[col]
        inverse = pow(rows[col][col] % p, -1, p)
        rows[col] = [value * inverse % p for value in rows[col]]
        for row in range(3):
            if row != col and rows[row][col] % p:
                factor = rows[row][col] % p
                rows[row] = [
                    (rows[row][k] - factor * rows[col][k]) % p for k in range(4)
                ]
    return rows[0][3], rows[1][3], rows[2][3]


def affine_on(values, points, xs, p):
    if len(points) <= 2:
        return True
    first, second = points[0], points[1]
    slope = (values[second] - values[first]) * pow((xs[second] - xs[first]) % p, -1, p) % p
    intercept = (values[first] - slope * xs[first]) % p
    return all((intercept + slope * xs[idx] - values[idx]) % p == 0 for idx in points)


def bad_set(n, xs, first, second, threshold, p):
    u0 = [pow(x, first, p) for x in xs]
    u1 = [pow(x, second, p) for x in xs]
    bad = set()
    for points in combinations(range(n), 4):
        solution = None
        for triple in combinations(points, 3):
            matrix = [[u1[i] % p, (-xs[i]) % p, (p - 1) % p] for i in triple]
            rhs = [(-u0[i]) % p for i in triple]
            candidate = solve3(matrix, rhs, p)
            if candidate is None:
                continue
            fourth = [index for index in points if index not in triple][0]
            gamma, slope, intercept = candidate
            if (intercept + slope * xs[fourth] - u0[fourth] - gamma * u1[fourth]) % p == 0:
                solution = candidate
            break  # a non-singular triple decides consistency of this 4-set
        if solution is None:
            continue
        gamma, slope, intercept = solution
        witness = [
            index for index in range(n)
            if (intercept + slope * xs[index] - u0[index] - gamma * u1[index]) % p == 0
        ]
        if len(witness) >= threshold and not (
            affine_on(u0, witness, xs, p) and affine_on(u1, witness, xs, p)
        ):
            bad.add(gamma)
    return bad


def ceiling_closed_form(n, xs, p):
    return {(-(xs[i] + xs[j] + xs[k])) % p for i, j, k in combinations(range(n), 3)}


def census(n, p):
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    ceiling = ceiling_closed_form(n, xs, p)
    counts = {
        (a, b): len(bad_set(n, xs, a, b, T_BELOW, p))
        for a in range(n) for b in range(n)
    }
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items() if count == maximum))
    return len(ceiling), maximum, winners


def main():
    print("independent cross-check: n=16 below-ceiling monomial-pencil census")
    results = {}
    for (n, p), expected in EXPECTED.items():
        observed = census(n, p)
        assert observed[0] == expected[0], (n, p, "ceiling", observed[0])
        assert observed[1] == expected[1], (n, p, "max", observed[1])
        if expected[2] is not None:
            assert observed[2] == expected[2], (n, p, "winners", observed[2])
        results[(n, p)] = observed

    prize_p = 21 * (2 ** 128) + 1
    assert pow(5, (prize_p - 1) // 2, prize_p) == prize_p - 1
    observed = census(N16, prize_p)
    assert observed == (464, 97, FOUR), observed

    print("(n, p) -> (ceiling, below max, maximizers)")
    for (n, p), observed in results.items():
        print(f"  ({n}, {p}) -> {observed}")
    print(f"  ({N16}, 21*2^128+1) -> {observed}")
    print("PASS: independent implementation reproduces every asserted integer")


if __name__ == "__main__":
    main()
