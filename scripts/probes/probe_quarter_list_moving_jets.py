"""Exact contact, interpolation and derivative-degree checks on the second field."""
from fractions import Fraction
from math import comb

from probe_quarter_coset_lists import require


def verify(n, exceptional, sections, subset, rank, z_degree, w_degree):
    u = (exceptional-4)//2
    multiple = exceptional-4
    D = (n-2*exceptional+4+1)//2
    b = z_degree+w_degree
    e = rank*b*u
    repeated = 2*u*comb(subset, 2)
    slope = subset-2-3-2*(z_degree+4*w_degree)
    twice_margin = slope*D - (subset-2)*2*u - 3*repeated - 2*multiple*subset - 4*e
    require(slope >= 0 and twice_margin > 0, 'zero count must exceed pole count')
    require(subset == rank-1 and rank <= (z_degree+1)*(w_degree+1), 'interpolation dimensions')
    require((2*w_degree-1)*e < D, 'derivative resultant cannot vanish at H')
    bezout = b*b*(1+2*u)
    component = (sections+b-1)//b
    require(bezout < component and subset <= component, 'insufficient isolated jets')
    return D, twice_margin, bezout, component


def verify_uniform_constants():
    # h = 2**20 (j+1)**4 and n/h >= 2**26 throughout this argument.
    length_per_h = 2**26
    require(2 * 25**2 * 26**2 < 2**20, 'quarter-rate fourth-moment cap')
    contact_loss = 157 * 8 + 24 * comb(159, 2) + 16 * 159 + 4 * 160 * 38 * 4
    require(10 * length_per_h > contact_loss, 'uniform contact count')
    require(3 * 15 * 160 * 38 * 4 < length_per_h, 'uniform resultant')
    require(100 * 38**3 * 9 < length_per_h, 'uniform isolated jets')
    for q, agreement in ((2, Fraction(7, 10)), (8, Fraction(1, 3)), (16, Fraction(1, 5))):
        rate = Fraction(1, q)
        require((agreement + Fraction(1, 1000))**2 <= rate - Fraction(1, 2**46),
                'uniform agreement floor')
        gap = agreement - rate
        require(gap >= Fraction(1, 8), 'uniform diagonal gap')
        require((rate - max(0, 2 * agreement - 1)) / gap <= Fraction(3, 4),
                'uniform support entry bound')
    require(2 * 49**2 * 50**2 < 7 * 2**46 // 16, 'uniform fourth-moment contradiction')


if __name__ == '__main__':
    verify_uniform_constants()
    result = verify(2**30, 3080, 1_072_766_345, 159, 160, 30, 8)
    print('Degree floor, doubled contact surplus, isolated-jet ceiling, forced jets:', *result)
