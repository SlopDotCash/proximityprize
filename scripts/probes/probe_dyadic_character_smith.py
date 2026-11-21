#!/usr/bin/env python3
"""Check the dyadic lifting bound by elimination over finite residue rings."""

from math import comb
from random import Random


def residual_block(kernel, modulus):
    """Eliminate every unit pivot of the cyclic convolution matrix."""
    size = len(kernel)
    matrix = [[kernel[(i - j) % size] % modulus for j in range(size)]
              for i in range(size)]
    for j in range(size):
        pivot = next(((a, b) for a in range(j, size) for b in range(j, size)
                      if matrix[a][b] % 2), None)
        if pivot is None:
            return [row[j:] for row in matrix[j:]]
        a, b = pivot
        matrix[a], matrix[j] = matrix[j], matrix[a]
        for row in matrix:
            row[b], row[j] = row[j], row[b]
        pivot_row = matrix[j]
        inv = pow(pivot_row[j], -1, modulus)
        for row in matrix[j + 1:]:
            scale = row[j] * inv % modulus
            if scale:
                for i in range(j, size):
                    row[i] = (row[i] - scale * pivot_row[i]) % modulus
    return []


def main():
    random = Random(296982)
    base = [comb(6, i) * (-1)**(6-i) for i in range(7)]
    for exponent in range(4, 8):
        size = 2**exponent
        modulus = size // 4
        for trial in range(4):
            if trial == 0:
                kernel = base + [0] * (size - len(base))
            else:
                # Odd augmentation makes the cofactor a unit modulo two.
                unit = [random.randrange(2) for _ in range(size)]
                unit[0] = (1 - sum(unit[1:])) % 2
                kernel = [sum(c * unit[(j-i) % size] for i, c in enumerate(base))
                          + 2 * random.randint(-size, size) for j in range(size)]
            residual = residual_block(kernel, modulus)
            assert len(residual) == 6 and all(len(row) == 6 for row in residual)
            assert not any(map(any, residual))
        first = residual_block(base + [0] * (size - 7), 2 * modulus)
        assert len(first) == 6 and any(map(any, first))
        print(f"n={size}: four independent eliminations mod {modulus}, "
              f"sharp example mod {2*modulus}")


if __name__ == "__main__":
    main()
