"""Exact interpolation, normalized pole and literal prime-field list bounds."""
from fractions import Fraction

from probe_first_order_integral_families import row_cost
from probe_quarter_coset_lists import require


def list_bound(b, v, d, n, t):
    slope = 4*b*v - 2*b - 2*v*v
    return 2*b*v - v*v + b + d*slope + Fraction(v*(n-d), t-d)


def source_slots(r, b, v, d, t):
    return sum(max(0, r*t - d*j - (d-1)*h) for h in range(v+1) for j in range(b-h+1))


def verify_fields():
    n = 2**30
    # Rate denominator, radius, jet board, budget, offset, generator witness, and slot surplus.
    cases = [
        (2, 318_582_739, 13, 18, 3, 81, 22, 3, 770),
        (4, 547_807_172, 12, 23, 3, 53, 28, 7, 494),
        (8, 706_542_381, 10, 27, 3, 32, 64, 5, 42),
        (16, 816_890_638, 7, 25, 4, 20, 95, 3, 325),
        (2, 319_220_543, 14, 19, 3, 89, 4, 11, 106),
        (4, 548_801_377, 10, 19, 4, 59, 10, 5, 850),
        (8, 708_016_270, 9, 22, 4, 35, 11, 3, 385),
        (16, 818_211_920, 8, 27, 4, 22, 89, 5, 850),
    ]
    for q, errors, r, b, v, c, h, a, surplus in cases:
        d, t = n//q-1, n-errors
        rows = n*row_cost(r, v)
        require(source_slots(r, b, v, d, t) - rows == surplus > 0, 'jet dimension')
        require(source_slots(r, b, v, d, t-1) <= rows, 'next error on the same board')
        cap = list_bound(b, v, d, n, t)
        require(cap <= c*n, 'normalized solution count')
        p = c*2**158 + h*2**100 + 1
        require(p > max(r*t+1, 2*b**3+2) and p//2**128 == c*n, 'field assumptions')
        require((p-1) % 2**100 == 0 and (2**100+1)**2 > p, 'prime divisor size')
        require(pow(a, (p-1)//2, p) == p-1, 'primality and exact dyadic generator')
        require(pow(pow(a, (p-1)//n, p), n//2, p) == p-1, 'order-n grid')
        print(f'1/{q}, {errors:,} errors, {surplus} slots spare, '
              f'{cap.numerator//cap.denominator:,} <= {c}n on p={p}')


def verify_local_counts():
    for b in range(1, 25):
        for v in range(1, b+1):
            ramification = (v-1)*(2*b-v)
            require(2*ramification + 2*(b-v) == 4*b*v-2*b-2*v*v, 'genus and pole charge')

    # V=1/Y, delta Y=V. Before each differentiation its single pole is
    # exactly of the indicated order. The normalized linear slope is attained.
    coefficient, power = 1, -1
    for order in range(16):
        require(coefficient != 0 and -power == 1+2*order, 'ordinary pole growth')
        coefficient *= power
        power -= 2


if __name__ == '__main__':
    verify_local_counts()
    verify_fields()
