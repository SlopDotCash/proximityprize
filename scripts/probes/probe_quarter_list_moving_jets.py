"""Exact contact, interpolation and derivative-degree checks on the second field."""
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


if __name__ == '__main__':
    result = verify(2**30, 3080, 1_072_766_345, 159, 160, 30, 8)
    print('Degree floor, doubled contact surplus, isolated-jet ceiling, forced jets:', *result)
