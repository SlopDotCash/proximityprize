#!/usr/bin/env python3
"""Exact sponsor-prime rank-5/rank-6 Wick/DC crossover checks for G262.

All load-bearing comparisons use integers or Fraction. Floating-point output is diagnostic only.
"""

from fractions import Fraction
from math import log, prod

N = 2**30
SPONSORS = {
    "P1": N * (2**128 + 192) + 1,
    "P2": N * (2**129 + 13) + 1,
}


def odd_double_factorial(r: int) -> int:
    return prod(range(1, 2 * r, 2))


def ratio_wick_to_dc(q: int, r: int) -> Fraction:
    # ((2r-1)!! * N^r) / (N^(2r)/q)
    return Fraction(odd_double_factorial(r) * q, N**r)


def main() -> None:
    assert N == 2**30
    for label, q in SPONSORS.items():
        assert N**5 < q < N**6
        beta = log(q) / log(N)
        print(f"{label}: q={q}")
        print(f"  log_N(q)={beta:.12f}; exact crossover N^5 < q < N^6")

        r5 = ratio_wick_to_dc(q, 5)
        r6 = ratio_wick_to_dc(q, 6)
        print(f"  r=5 Wick/DC={float(r5):.15f} ({r5.numerator}/{r5.denominator})")
        print(f"  r=6 Wick/DC={float(r6):.15f} ({r6.numerator}/{r6.denominator})")

        if label == "P1":
            assert r5 > 241_920
            assert r6 < Fraction(1, 400)
            assert 400 * odd_double_factorial(6) * N**6 * q < N**12
            print("  exact margins: Wick_5 > 241920*DC_5; DC_6 > 400*Wick_6")
        else:
            assert r5 > 483_840
            assert r6 < Fraction(1, 200)
            assert 200 * odd_double_factorial(6) * N**6 * q < N**12
            print("  exact margins: Wick_5 > 483840*DC_5; DC_6 > 200*Wick_6")

        # FS/G64 direction: at r=6 the principal DC mass alone exceeds raw Wick.
        assert odd_double_factorial(6) * q < N**6
        # G63 consequence: any census C with DC <= C is necessarily super-Wick by the same factor.
        print("  consequence: every C >= DC_6 is strictly super-Wick at rank 6")

    # The direction really flips between adjacent live ranks at both sponsors.
    assert all(ratio_wick_to_dc(q, 5) > 1 for q in SPONSORS.values())
    assert all(ratio_wick_to_dc(q, 6) < 1 for q in SPONSORS.values())
    print("PASS: exact sponsor rank-5/rank-6 crossover verified")


if __name__ == "__main__":
    main()
