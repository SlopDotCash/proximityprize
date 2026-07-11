#!/usr/bin/env python3
"""Exact audit of the depth-seven repeated-coordinate Newton/Hölder reduction.

The script derives the ordered-distinct Newton polynomial D_7 from the recurrence

  D_r = sum_{j=1}^r (-1)^(j-1) (r-1)!/(r-j)! p_j D_{r-j},

expands p_1^14-D_7^2, groups absolute coefficients by the number of power-sum
factors, and checks the production barrier arithmetic.  All polynomial and
population calculations are exact integers/rationals.  Decimal output is only a
human-readable rendering of already checked inequalities.
"""

from __future__ import annotations

from collections import defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from math import factorial, prod


VARIABLES = 7
ZERO = (0,) * VARIABLES
EXPECTED_MASSES = {
    13: 42,
    12: 791,
    11: 8_820,
    10: 64_743,
    9: 328_986,
    8: 1_184_153,
    7: 3_034_920,
    6: 5_482_456,
    5: 6_787_872,
    4: 5_450_256,
    3: 2_540_160,
    2: 518_400,
}


def add(*polynomials: dict[tuple[int, ...], int]) -> dict[tuple[int, ...], int]:
    out: defaultdict[tuple[int, ...], int] = defaultdict(int)
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            out[monomial] += coefficient
    return {monomial: coefficient for monomial, coefficient in out.items() if coefficient}


def scale(polynomial: dict[tuple[int, ...], int], scalar: int) -> dict[tuple[int, ...], int]:
    return {
        monomial: scalar * coefficient
        for monomial, coefficient in polynomial.items()
        if scalar * coefficient
    }


def mul(
    left: dict[tuple[int, ...], int], right: dict[tuple[int, ...], int]
) -> dict[tuple[int, ...], int]:
    out: defaultdict[tuple[int, ...], int] = defaultdict(int)
    for monomial_left, coefficient_left in left.items():
        for monomial_right, coefficient_right in right.items():
            monomial = tuple(a + b for a, b in zip(monomial_left, monomial_right))
            out[monomial] += coefficient_left * coefficient_right
    return {monomial: coefficient for monomial, coefficient in out.items() if coefficient}


def variable(j: int) -> dict[tuple[int, ...], int]:
    monomial = [0] * VARIABLES
    monomial[j - 1] = 1
    return {tuple(monomial): 1}


def polynomial_power(polynomial: dict[tuple[int, ...], int], exponent: int):
    out = {ZERO: 1}
    for _ in range(exponent):
        out = mul(out, polynomial)
    return out


def distinct_polynomials() -> list[dict[tuple[int, ...], int]]:
    result = [{ZERO: 1}]
    for r in range(1, 8):
        terms = []
        for j in range(1, r + 1):
            coefficient = (-1) ** (j - 1) * factorial(r - 1) // factorial(r - j)
            terms.append(scale(mul(variable(j), result[r - j]), coefficient))
        result.append(add(*terms))
    return result


def seventh_root_two() -> Decimal:
    getcontext().prec = 80
    x = Decimal("1.1041")
    two = Decimal(2)
    seven = Decimal(7)
    for _ in range(40):
        x = (Decimal(6) * x + two / (x**6)) / seven
    assert abs(x**7 - two) < Decimal("1e-70")
    return x


def normalized_holder_value(root: Decimal) -> tuple[Decimal, Decimal]:
    """Return F(C)/(q*n^7) and its derivative in C at C=2^18."""
    getcontext().prec = 80
    c = Decimal(2**18)
    n = Decimal(2**30)
    value = Decimal(0)
    slope = Decimal(0)
    for k, coefficient in EXPECTED_MASSES.items():
        exponent_c = Decimal(k) / Decimal(14)
        term = Decimal(coefficient) * (c**exponent_c) * (
            n ** (Decimal(k) / 2 - 7)
        )
        value += term
        slope += exponent_c * term / c
    # Independent check using the single algebraic root 2^(1/7).
    value_from_root = Decimal(0)
    for k, coefficient in EXPECTED_MASSES.items():
        numerator = 114 * k - 1470
        quotient, remainder = divmod(numerator, 7)
        value_from_root += Decimal(coefficient) * (Decimal(2) ** quotient) * root**remainder
    assert abs(value - value_from_root) < Decimal("1e-60")
    return value, slope


def main() -> None:
    distinct = distinct_polynomials()
    d7 = distinct[7]
    assert len(d7) == 15
    assert sum(abs(coefficient) for coefficient in d7.values()) == factorial(7)
    assert d7[(7, 0, 0, 0, 0, 0, 0)] == 1
    assert d7[(5, 1, 0, 0, 0, 0, 0)] == -21

    repeated = add(polynomial_power(variable(1), 14), scale(mul(d7, d7), -1))
    masses: defaultdict[int, int] = defaultdict(int)
    term_counts: defaultdict[int, int] = defaultdict(int)
    for monomial, coefficient in repeated.items():
        block_count = sum(monomial)
        masses[block_count] += abs(coefficient)
        term_counts[block_count] += 1
    assert dict(masses) == EXPECTED_MASSES
    assert sum(masses.values()) == 25_401_599
    assert len(repeated) == 88
    assert repeated[(12, 1, 0, 0, 0, 0, 0)] == 42
    assert repeated[(10, 2, 0, 0, 0, 0, 0)] == -651
    assert repeated[(11, 0, 1, 0, 0, 0, 0)] == -140

    x = 2**15
    coarse_ratio = sum(Fraction(coefficient, x ** (14 - k)) for k, coefficient in masses.items())
    assert coarse_ratio < Fraction(1, 779)
    assert not coarse_ratio < Fraction(1, 780)

    # Rational upper certificate for 2^(1/7).  Since t^7>2, t is an upper bound.
    t = Fraction(5521, 5000)
    assert t**7 > 2
    rational_upper = Fraction(0)
    for k, coefficient in masses.items():
        numerator = 114 * k - 1470
        quotient, remainder = divmod(numerator, 7)
        power_of_two = Fraction(2**quotient) if quotient >= 0 else Fraction(1, 2 ** (-quotient))
        rational_upper += coefficient * power_of_two * t**remainder
    assert rational_upper < 138

    root = seventh_root_two()
    holder_value, holder_slope = normalized_holder_value(root)
    assert holder_value < 138
    assert holder_slope < Decimal(1) / Decimal(1024)

    n = 2**30
    m = 2**128 + 192
    q = n * m + 1
    falling = lambda depth: prod(n - j for j in range(depth))
    repeated_population = n**14 - falling(7) ** 2
    exact_one_repeat_population = 42 * falling(6) * falling(7)
    corrected_slack = q * 127_009 * n**7
    remainder_population = repeated_population - exact_one_repeat_population
    assert 1386 * corrected_slack < repeated_population < 1387 * corrected_slack
    assert 45_096 * remainder_population < corrected_slack
    assert not 45_097 * remainder_population < corrected_slack

    print("BGK_REPEATED_NEWTON_ABSORPTION")
    print(f"D7Terms={len(d7)}; D7CoefficientL1={sum(abs(c) for c in d7.values())}")
    print(f"repeatedTerms={len(repeated)}; repeatedCoefficientL1={sum(masses.values())}")
    print("blockCount:termCount:coefficientL1")
    for k in sorted(masses, reverse=True):
        print(f"{k}:{term_counts[k]}:{masses[k]}")
    print("leading=42*p2*p1^12-651*p2^2*p1^10-140*p3*p1^11")
    print(f"coarseProductionRatio={float(coarse_ratio):.15f}")
    print("coarseCertificate=<1/779 and not <1/780")
    print(f"rootUpper={t}; rootUpperPow7={float(t**7):.15f}")
    print(f"holderCoefficientUpper={float(rational_upper):.15f}<138")
    print(f"holderCoefficientActual={holder_value:.15f}")
    print(f"holderTangentSlope={holder_slope:.15f}<1/1024")
    print(f"repeatedPopulationOverSlack={repeated_population / corrected_slack:.15f}")
    print(f"exactOneRepeatShare={exact_one_repeat_population / repeated_population:.15f}")
    print(f"beyondOneRepeatSlackInverse={corrected_slack / remainder_population:.15f}")
    print("barrierSplit=126871+138=127009")


if __name__ == "__main__":
    main()
