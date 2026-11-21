#!/usr/bin/env python3
"""Check scalar and interleaved list budgets by exhaustive coset enumeration.

The prime-field RS code can interpolate the first k symbols of any centre.
Subtracting that codeword in each row leaves a unique centre with its first
k symbols zero. Translation preserves every list size, so these representatives
cover the entire space of received words.
"""

from itertools import accumulate, product
from math import comb


def list_profile(prime, domain, dimension, arity):
    """Maximum closed-ball list size for every absolute Hamming radius."""
    length = len(domain)
    code = [
        tuple(
            sum(c * pow(x, j, prime) for j, c in enumerate(coefficients)) % prime
            for x in domain
        )
        for coefficients in product(range(prime), repeat=dimension)
    ]
    words = list(product(code, repeat=arity))
    columns = list(product(range(prime), repeat=arity))

    # Represent a vector symbol by its index in the row-major Cartesian power.
    symbol_id = {column: index for index, column in enumerate(columns)}
    words = [tuple(symbol_id[col] for col in zip(*rows)) for rows in words]
    maximum = [0] * (length + 1)
    for tail in product(range(len(columns)), repeat=length - dimension):
        centre = (0,) * dimension + tail
        counts = [0] * (length + 1)
        for word in words:
            counts[sum(x != y for x, y in zip(centre, word))] += 1
        maximum = list(map(max, maximum, accumulate(counts)))
    return maximum


def main():
    boards = [
        (2, (0, 1), 1, 3),
        (3, (0, 1, 2), 2, 2),
        (5, (1, 2, 4, 3), 2, 2),
        (7, (1, 2, 4), 2, 2),
    ]
    for prime, domain, dimension, arity in boards:
        scalar = list_profile(prime, domain, dimension, 1)
        interleaved = list_profile(prime, domain, dimension, arity)
        budgets = [b for b in range(prime + 1) if comb(b + 1, 2) <= prime]
        nonzero_weights = prime**arity - 1
        kernel_weights = prime ** (arity - 1) - 1
        for errors, (base, inter) in enumerate(zip(scalar, interleaved)):
            if base > inter:
                raise ArithmeticError("diagonal embedding bound failed")
            # Collision expectation for a uniform nonzero row functional.
            if inter * (nonzero_weights - base * kernel_weights) > base * (
                nonzero_weights - kernel_weights
            ):
                raise ArithmeticError("row collision bound failed")
            agreement = len(domain) - errors
            if agreement >= dimension:
                directions = errors // (agreement - dimension + 1)
                rhs = base * (
                    prime**2 - 1 + (prime - 1) * directions * (base - 1)
                )
                if inter * (prime**2 - base) > rhs:
                    raise ArithmeticError("rank-one direction bound failed")
            for budget in budgets:
                if (base <= budget) != (inter <= budget):
                    raise ArithmeticError(f"list-budget equivalence failed at {budget=}")
        print(
            f"F_{prime} n={len(domain)} k={dimension} m={arity} "
            f"budgets={budgets} scalar={scalar} interleaved={interleaved}"
        )


if __name__ == "__main__":
    main()
