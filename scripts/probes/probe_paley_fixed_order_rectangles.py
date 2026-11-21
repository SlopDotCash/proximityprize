#!/usr/bin/env python3
"""Check cubic and quartic determinant orders and prescribed rectangles over F_13."""

from itertools import combinations

from probe_paley_shift_multiplicities import (
    determinant, jet_polynomials, require, translated_coefficients,
)


def check(order, sites):
    p, a = 13, len(sites)
    d = (p - 1) // order
    # 2 generates F_13^*. These colors correspond to successive complex roots of unity.
    colors = [pow(2, j * d, p) for j in range(order)]
    rows = [[pow((b + u) % p, d, p) for u in sites] for b in range(p)]
    totals = [[row.count(color) for color in colors] for row in rows]
    zeros = [row.count(0) for row in rows]
    shifts = rectangles = 0

    for x in range(1, a // 2 + 1):
        for j, color in enumerate(colors):
            poly = determinant(jet_polynomials(sites, d + a - 1, x, color, p), x, p)
            require(len(poly) - 1 == x * (d + 1 - x), (sites, order, color, x, "degree"))
            for b in range(p):
                e = a - zeros[b] - totals[b][j]
                charge = max(0, x-e) * max(0, a-x-e)
                translated = translated_coefficients(poly, b, p)
                require(all(c == 0 for c in translated[:charge]), (sites, order, b, "order"))
                shifts += 1

        for bsize in range(1, p + 1):
            R = bsize**2 * (a-2*x)**2 + 4*bsize*x*(d+1-x)
            area = a*bsize
            for subset in combinations(range(p), bsize):
                n = [sum(totals[b][j] for b in subset) for j in range(order)]
                z = sum(zeros[b] for b in subset)
                require(max(0, 2*max(n)-area+2*z)**2 <= R, (sites, order, subset, "color"))
                if order == 3:
                    u, v = n[0]-n[2], n[1]-n[2]
                    norm_sq = u*u - u*v + v*v
                    bound = 4*norm_sq <= area**2 + 3*R
                else:
                    norm_sq = (n[0]-n[2])**2 + (n[1]-n[3])**2
                    bound = 2*norm_sq <= area**2 + R
                require(bound, (sites, order, subset, "complex norm"))
                rectangles += 1
    return shifts, rectangles


if __name__ == "__main__":
    cases = [check(k, sites) for k in (3, 4) for sites in ((0, 1), (0, 1, 4, 6))]
    print(f"{sum(s for s, _ in cases)} local determinant orders and "
          f"{sum(r for _, r in cases)} rectangle/parameter tests passed")
