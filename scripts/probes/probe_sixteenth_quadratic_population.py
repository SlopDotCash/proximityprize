#!/usr/bin/env python3
"""Certify the second named list budget using the population of its quadratic component."""
from fractions import Fraction

from probe_joint_list_contact_boards import linear
from probe_linear_contact_quotient import N, rank, require, slots
from probe_low_rate_named_adaptive_cofactors import curve_bound
from probe_sixteenth_factor_contact_orders import contact_intervals


def verify():
    d = N // 16 - 1
    errors = 820_050_000
    t = N - errors
    primary = 9 * t
    b = (primary - 1) // (d - 1)
    stock = N // 20
    budget = 2 * N
    primary_surplus = slots(primary, 4, d) - N * rank(9, 4)
    require(primary_surplus > 0 and 4 * stock + b <= budget, 'primary or small groups')
    require(stock > b * ((3000 * t - 1) // (d - 1)), 'linear secondary Bezout')
    linear_gain = linear(d, t, primary, b, 10, False)
    require(curve_bound(9, 1, d, t) + 3 * stock + b <= budget, 'linear low weights')

    gains = {}
    for v, ceiling, cutoff in [(2, 6, 13), (3, 4, 5), (4, 4, 5)]:
        require(curve_bound(ceiling, v, d, t) + (4-v) * stock + b <= budget,
                f'low-weight list budget at derivative degree {v}')
        gains[v] = contact_intervals(v, cutoff * (d-1), primary-1, t, d, b, stock)

    # In the middle window the total (Y,V)-degree is at most 13.
    # On two V-linear factors, sum their bounds before maximizing over the split.
    total = 13
    split = 3 * total - 2 + (2 * total - 4) * d + 2 * Fraction(N-d, t-d)
    for first in range(1, total):
        require(curve_bound(first, 1, d, t) + curve_bound(total-first, 1, d, t) == split,
                'componentwise bound')
    require(split + 2 * stock + b <= budget, 'split quadratic budget')

    # A putative overrun assigns every remaining word to the one irreducible factor.
    population = budget + 1 - 2 * stock - b
    boards = [(6440, 2424), (6750, 2070)]
    lo, hi = 7 * (d-1), 13 * (d-1)
    middle = contact_intervals(2, lo, hi, t, d, b, population, r=24000, boards=boards)
    print(f'Safe through {errors:,} errors; cap {budget:,}; primary surplus {primary_surplus:,}.')
    print(f'Linear surplus {linear_gain:,}; high-weight surpluses {gains}.')
    print(f'Quadratic population {population:,}; split budget {int(split + 2*stock + b):,}; '
          f'middle surplus {middle:,}.')


if __name__ == '__main__':
    verify()
