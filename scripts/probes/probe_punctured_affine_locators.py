#!/usr/bin/env python3
"""Check the four explicit affine targets and their punctured list over F_17."""
from math import prod

PRIME = 17
A = (3, 15, 8, 12, 6, 1)
B = (7, 3, 0, 12, 3)
TARGETS = ((0, 0), (1, 4), (9, 2), (15, 3))
SUPPORTS = ((2, 3, 4, 5, 14), (4, 6, 7, 9, 15),
            (2, 6, 11, 12, 13), (3, 9, 10, 13, 16))


def evaluate(coeffs, x):
    return sum(c * pow(x, i, PRIME) for i, c in enumerate(coeffs)) % PRIME


def main():
    domain = range(2, PRIME)
    values = [(evaluate(A, x), evaluate(B, x)) for x in domain]
    for (slope, root), support in zip(TARGETS, SUPPORTS):
        roots = tuple(x for x, (a, b) in zip(domain, values) if (a+slope*(x-root)*b) % PRIME == 0)
        if roots != support:
            raise ArithmeticError(f"incorrect locator {roots}")
    # A has five distinct roots; checking B there certifies coprimality over the closure.
    if any(evaluate(B, x) == 0 for x in SUPPORTS[0]):
        raise ArithmeticError("unexpected common factor")
    heads = ((), (8, 10, 11, 12, 13, 16), (7, 8, 9, 10, 15, 16), (6, 7, 8, 11, 12, 15))
    scale = (0, 1, 11, 5)
    counts = [0] * 4
    for x in domain:
        row = [c * prod(x-a for a in roots) % PRIME for c, roots in zip(scale, heads)]
        matched = {v for v, support in zip(row, SUPPORTS) if x not in support}
        if len(matched) != 1:
            raise ArithmeticError(f"no common received value at {x}")
        for i, v in enumerate(row):
            counts[i] += v in matched
    if counts != [10]*4:
        raise ArithmeticError(counts)
    print("Four full affine fibers of degree five and four sextics at ten agreements verified.")


if __name__ == "__main__":
    main()
