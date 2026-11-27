"""Verify the two-direction contact argument at the second-prime quarter-rate endpoint."""
from fractions import Fraction


def check_endpoint():
    n = 2**30
    degree = n // 4 - 1
    agreements = 2 * degree - 5
    messages = 2 * n + 1
    gap = agreements - degree
    upper = 1 + Fraction(messages * (n * degree - agreements**2), n * gap)
    energy = 2 * upper * (upper - 1) * (upper + 1)**2

    def matching(threshold):
        mu = Fraction(degree - threshold, gap)
        kappa = Fraction(degree, gap)
        assert 0 < mu < 1
        assert 3 * agreements - n - 2 * (threshold - 1) > degree
        lower = ((1 - mu**2) * messages - energy) / (2 * kappa**2 * (kappa**2 - mu**2))
        return lower.numerator // lower.denominator

    tight, broad = 736_083, 50_000_000
    small, large = matching(tight), matching(broad)
    holes = n - 2 * agreements + tight - 1
    broad_holes = n - 2 * agreements + broad - 1
    assert (small, large) == (100_456, 1_056_336_697)
    assert (holes, broad_holes) == (736_096, 50_000_013)
    assert n - 2 * holes - broad_holes > 3 * degree
    exceptional = 2_513_196
    for x in range(exceptional + 1, 4 * holes - 3):
        pair_overlap = (x - 4) // 2
        hits = x - holes
        assert small * (hits**2 - x * pair_overlap) > x * (hits - pair_overlap)

    u = (exceptional - 4) // 2
    multiple = exceptional - 4
    d_min = (n - 2 * exceptional + 4) // 2
    odd = degree + 2 * multiple
    e, offset, r, reverse = 74_000_000, 14 * u, 61, 15
    monomials = [(k, l) for k in range(18) for l in range(5)
                 if k + l <= 17 and 2 * k + 3 * l <= 35]
    variables = sum(max(0, min(e, e + offset - (k + l) * u) + 1) for k, l in monomials)
    equations = r * (e + offset + 1)
    assert (len(monomials), variables, equations) == (76, 5_600_124_752, 5_587_133_045)
    assert variables > equations
    forward_margin = ((r - 35 - 4 * 4) * d_min - 2 * u * r - u * r * (r - 1)
                      - odd - 2 * multiple - 4 * e)
    reverse_margin = (reverse * (d_min - 2 * u) - u * reverse * (reverse - 1)
                      - odd - 2 * reverse * multiple - 4 * reverse * (e + 17 * u))
    assert (forward_margin, reverse_margin) == (16_642_885, 1_643_197_211)
    assert d_min > 7 * e
    assert large - 2 - (reverse - 1) > 17**2 * (1 + 2 * u)
    assert 2 * (u + 1) < 2**32
    print(f'{n - agreements:,} errors, {large:,} sections, '
          f'{variables - equations:,} more variables than equations')
    print(f'Twice the forward and aggregate reverse zero-degree margins are '
          f'{forward_margin:,} and {reverse_margin:,}.')


if __name__ == '__main__':
    check_endpoint()
