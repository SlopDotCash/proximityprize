#!/usr/bin/env python3
"""Recompute the order-two symbolic interpolation and recovery budgets in integers."""

from fractions import Fraction


WITNESS_PRIME = 126205134105047729256068842055334737587878534445324289139206048206460929


def profile(n, k, agreement, multiplicity, derivative_weight, *, coarse_degree=None):
    """Count the source and the smaller side of each local Taylor bidegree block."""
    degree = k - 1 if coarse_degree is None else coarse_degree
    cutoff = multiplicity * agreement
    dimension = 0
    jet_cap = 0
    source = {}
    for second in range(derivative_weight // 2 + 1):
        for first in range(derivative_weight - 2 * second + 1):
            derivative_degree = first + 2 * second
            remaining = cutoff - degree * (first + second)
            for value in range((remaining - 1) // degree + 1):
                width = remaining - value * degree
                dimension += width
                total = value + first + second
                jet_cap = max(jet_cap, total)
                for power in range(min(width, multiplicity + derivative_degree)):
                    block = total, power - derivative_degree
                    source[block] = source.get(block, 0) + 1

    def target_rows(total, shift):
        number = 0
        for error in range(total + 1):
            # Remaining degrees satisfy first + second = total - error.
            # The Taylor exponent is shift + total + second + 2*error.
            lower = max(0, -shift - total - 2 * error)
            upper = min(total - error, multiplicity - 1 - shift - total - 2 * error)
            number += max(0, upper - lower + 1)
        return number

    local_rank_bound = sum(min(columns, target_rows(*block)) for block, columns in source.items())
    rank_bound = n * local_rank_bound
    assert rank_bound < dimension
    height = rank_bound * jet_cap // (dimension - rank_bound)
    gap = Fraction(agreement - k, n)
    coefficient = height + 4 * jet_cap**4 / gap**2 * (33 * height / gap + 3)
    required_field = 2**128 * n**3 * coefficient
    assert required_field <= WITNESS_PRIME
    return dimension, local_rank_bound, jet_cap, height, required_field


def main():
    cases = [
        # length, dimension, agreement, multiplicity, derivative-order cap
        ((1024, 512, 700, 112, 49), (2799856150, 2732779, 153, 287261)),
        ((262144, 131072, 180224, 54, 23), (41164959316, 156586, 74, 25988)),
        ((262144, 131072, 180160, 58, 25), (55063229494, 209400, 79, 25467)),
    ]
    for args, expected in cases:
        result = profile(*args)
        assert result[:4] == expected, (args, result[:4], expected)
        n, k, agreement, _, _ = args
        field_floor = (result[4].numerator + result[4].denominator - 1) // result[4].denominator
        print(f'n={n} k={k} agreement={agreement} errors={n-agreement} '
              f'columns={result[0]} rank_per_site={result[1]} jet_cap={result[2]} '
              f'height={result[3]} field_suffices={field_floor}')

    # Scaling D=k gives the same origin rank and height at every positive multiple.
    scaled_rows = [
        (2048, 2815, 58, 25, (860354222, 209400, 79, 25551), 20007104463588681),
        (1024, 1893, 51, 31, (881619592, 213977, 94, 15936), 17198307386709643),
        (512, 1279, 40, 30, (480983040, 116314, 99, 10341), 19969708005140362),
        (256, 875, 28, 25, (163920484, 39404, 95, 6080), 18940036421599633),
    ]
    for k, agreement, multiplicity, cap, expected, ceiling in scaled_rows:
        result = profile(4096, k, agreement, multiplicity, cap, coarse_degree=k)
        assert result[:4] == expected
        cost = result[4] / (2**128 * 4096**3)
        assert (cost.numerator + cost.denominator - 1) // cost.denominator == ceiling
        assert ceiling * (2**18)**3 * 2**128 <= WITNESS_PRIME
        print(f'n=4096*b k={k}*b errors={4096-agreement}*b coefficient={ceiling}')


if __name__ == '__main__':
    main()
