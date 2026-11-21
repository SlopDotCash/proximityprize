#!/usr/bin/env python3
"""Check the integer constants in the quadratic-discriminant MCA bound."""

from fractions import Fraction
from math import ceil

N = 2**30
D = 2**26 - 1
H = 2**21
T = 425_022_954
E = N - T
M = E + 2
L = 8_388_607


def main():
    monomials = sum((T - j * D) * (H + 1 - j) for j in range(3))
    surplus = monomials - N * (H + 1)
    universal = 2 * D + 1 - ceil(Fraction((2 * H + 2) * N, M))
    linear_universal = T - ceil(Fraction((H + 1) * N, M))
    exceptions = H * N // (L + 1)
    upper = 16 * H + 2 * (E + 1 + exceptions)
    checks = (
        surplus == 2_097_150,
        universal == 127_275_425,
        linear_universal >= universal,
        universal - 3 * L > D,
        exceptions == 268_435_456,
        upper == 1_867_863_086,
        upper <= 2 * N,
        E + 1 == 648_718_871,
    )
    if not all(checks):
        raise ArithmeticError("quadratic-discriminant count mismatch")
    print(f"surplus {surplus}, common sites {universal}, exceptional rows {exceptions}")
    print(f"bad scalars at {E} errors <= {upper}, budget {2*N}")
    print(f"supremum >= {E+1}/{N}")


if __name__ == "__main__":
    main()
