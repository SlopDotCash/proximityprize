#!/usr/bin/env python3
"""Exact CTR/positive-definite no-go cell for the depth-seven BGK residual.

The computation is integer-only.  For the multiplicative subgroup ``G`` of
``F_13313^*`` of order 256, let ``f_k`` count ordered k-tuples from ``G`` by
their additive sum.  Put

    C_6(delta) = sum_x f_6(x) f_6(x + delta),
    D(delta)   = p C_6(delta) - n^12.

``D`` is a centered additive autocorrelation, hence has zero global mean and
nonnegative additive Fourier transform.  The script verifies the remaining
finite identities without floating point arithmetic and emits the reduced
rational coefficient of the depth-seven defect.
"""

from fractions import Fraction


P = 13_313
N = 256
TARGET_COEFFICIENT = 2**18


def prime_factors(value: int) -> list[int]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    return factors


def primitive_root(prime: int) -> int:
    factors = prime_factors(prime - 1)
    return next(
        candidate
        for candidate in range(2, prime)
        if all(pow(candidate, (prime - 1) // factor, prime) != 1 for factor in factors)
    )


def subgroup(prime: int, order: int) -> tuple[int, int, list[int]]:
    assert (prime - 1) % order == 0
    generator = primitive_root(prime)
    step = (prime - 1) // order
    subgroup_generator = pow(generator, step, prime)
    values: list[int] = []
    value = 1
    for _ in range(order):
        values.append(value)
        value = value * subgroup_generator % prime
    assert value == 1
    assert len(set(values)) == order
    return generator, subgroup_generator, values


def convolve_with_subgroup(counts: list[int], group: list[int], prime: int) -> list[int]:
    result = [0] * prime
    for residue, count in enumerate(counts):
        if count:
            for element in group:
                result[(residue + element) % prime] += count
    return result


def main() -> None:
    generator, subgroup_generator, group = subgroup(P, N)

    counts = [0] * P
    counts[0] = 1
    layers: list[list[int]] = []
    for depth in range(1, 8):
        counts = convolve_with_subgroup(counts, group, P)
        assert sum(counts) == N**depth
        layers.append(counts)

    f6 = layers[5]
    f7 = layers[6]

    # Multiplicative G-invariance of f_6 is an exact finite certificate for
    # G-invariance of its additive autocorrelation D.
    assert all(f6[element * residue % P] == f6[residue] for element in group for residue in range(P))

    energy7 = sum(count * count for count in f7)
    correlation0 = sum(count * count for count in f6)
    defect0 = P * correlation0 - N**12

    # Only the translate set 1-G is needed.  This avoids materializing all
    # P autocorrelation values while still checking the signed restriction.
    restriction_correlation = sum(
        sum(f6[residue] * f6[(residue + 1 - element) % P] for residue in range(P))
        for element in group
    )
    assert N * restriction_correlation == energy7

    restriction = P * restriction_correlation - N**13
    centered_numerator = P * energy7 - N**14
    assert N * restriction == centered_numerator

    # Global mean follows by an exact convolution identity:
    # sum_delta C_6(delta) = (sum_x f_6(x))^2 = n^12.
    correlation_global_sum = sum(f6) ** 2
    defect_global_sum = P * correlation_global_sum - P * N**12
    assert defect_global_sum == 0

    denominator = P * N**7
    coefficient = Fraction(centered_numerator, denominator)
    margin = centered_numerator - TARGET_COEFFICIENT * denominator
    assert margin > 0

    print("BGK centered-translate positive-definite no-go certificate")
    print(f"p={P}")
    print(f"n={N}")
    print(f"primitive_root={generator}")
    print(f"subgroup_generator={subgroup_generator}")
    print(f"subgroup_step={(P - 1) // N}")
    print(f"subgroup_order={len(group)}")
    print(f"subgroup_weighted_checksum={sum((index + 1) * value for index, value in enumerate(group))}")
    print(f"sum_f6={sum(f6)}")
    print(f"sum_f7={sum(f7)}")
    print(f"E7={energy7}")
    print(f"C6_zero={correlation0}")
    print(f"D_zero={defect0}")
    print(f"restriction_correlation={restriction_correlation}")
    print(f"restriction_D={restriction}")
    print(f"centered_numerator={centered_numerator}")
    print(f"normalizing_denominator={denominator}")
    print(f"reduced_coefficient={coefficient.numerator}/{coefficient.denominator}")
    print(f"coefficient_decimal={float(coefficient):.12f}")
    print(f"target_coefficient={TARGET_COEFFICIENT}")
    print(f"positive_margin={margin}")
    print(f"global_mean_D={defect_global_sum}")
    print("fourier_nonnegative=centered_autocorrelation_identity")
    print("multiplicative_G_invariant=verified_on_all_3408128_pairs")
    print("status=COUNTEREXAMPLE_TO_2^18_N7_STRUCTURAL_BOUND")


if __name__ == "__main__":
    main()
