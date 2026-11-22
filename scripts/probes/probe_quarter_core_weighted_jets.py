#!/usr/bin/env python3
"""Check the quarter-rate interpolation orders and residual factor allocations."""
from functools import cache

from probe_tangent_head_windows import N, Window, check, tangent_cap


ERRORS = 525_150_000
PRIMARY = (11, 22, 21569)
COMPANION = (22, 44, 379)
RESIDUAL = (23, 40, 301)


def jet_rows(order, scalar_degree):
    return sum((order - j) * (scalar_degree + 1 - j) for j in range(order))


def main():
    window = Window(4, ERRORS, PRIMARY, COMPANION)
    r, v, s = RESIDUAL
    weight = r * window.t - 6 * window.d
    saved = jet_rows(r, s) - jet_rows(r - 2, s)
    correction = 4 * (s + 1)
    for owners in range(4):
        check(jet_rows(r - 2 * owners, s) + owners * saved <=
              jet_rows(r, s) + owners * (owners - 1) // 2 * correction, 'per-site jet count')
    columns = sum((s + 1 - j) * max(0, weight - j * window.d) for j in range(v + 1))
    rows = N * jet_rows(r, s) - 3 * window.core * saved + 3 * window.d * correction
    check(columns - rows == 2_168_061_014, 'residual rank surplus')
    check(window.surpluses == (7_694_423, 2_503_215_374), 'ordinary rank surpluses')
    check(window.group == 3 and window.cutoff > PRIMARY[2]*v + PRIMARY[1]*s,
          'collinear rich cores and residual divisibility')
    worst, count = (0, ()), 0
    for j in range(PRIMARY[1] + 1):
        for total in range(j, PRIMARY[1] + 1):
            m = min(COMPANION[2] - j, s) if j >= 3 else COMPANION[2] - j

            def price(b):
                bound = PRIMARY[0] * window.t - 1 - (total - b) * window.d
                if b == 1 or bound < b * window.d or m < b:
                    return window.cutoff
                return max(window.cutoff, tangent_cap(b, m, bound, window.t, window.d))

            @cache
            def pack(degree):
                if not degree:
                    return 0, ()
                return max((price(b) + pack(degree - b)[0], (b,) + pack(degree - b)[1])
                           for b in range(1, degree + 1))

            value, parts = pack(total - j)
            population = PRIMARY[2] + window.affine_mass(j) + value
            check(population <= 2 * N, 'factor allocation')
            worst = max(worst, (population, (j, parts)))
            count += 1
    check(worst == (2_081_389_015, (3, (19,))), 'maximum at three heads plus degree nineteen')
    print('Mixed-jet rank surpluses:', *window.surpluses, columns - rows)
    print('Checked all partitions across', count, 'degree and head-count choices.')
    print('Maximum bad labels:', worst[0], 'at', ERRORS, 'errors.')


if __name__ == '__main__':
    main()
