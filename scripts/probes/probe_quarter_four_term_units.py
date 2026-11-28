#!/usr/bin/env python3
"""Check the named quarter-rate list cap from the four-term unit equation."""

from fractions import Fraction as F

from probe_linear_contact_quotient import N, require
from probe_quarter_first_rational_observable import verify


def determinant(columns):
    x, y, z = columns
    return (x[0]*(y[1]*z[2]-z[1]*y[2]) - y[0]*(x[1]*z[2]-z[1]*x[2])
            + z[0]*(x[1]*y[2]-y[1]*x[2]))


def wronskian_controls():
    # u=X, v=X² and w=1-X-X² are independent and have common unit support
    # H=X(1-X-X²). Evaluate the cleared logarithmic Cramer system over Q.
    for x in range(2, 10):
        jets = [(x, 1, 0), (x*x, 2*x, 2), (1-x-x*x, -1-2*x, -2)]
        H = x*(1-x-x*x)
        columns = [(1, F(H*first, value), F(H**2*second, value))
                   for value, first, second in jets]
        det = determinant(columns)
        require(det != 0, 'independent unit Wronskian')
        for i, (value, _, _) in enumerate(jets):
            replaced = columns.copy()
            replaced[i] = (1, 0, 0)
            require(determinant(replaced) == det*value, 'three-term Cramer system')
        # The dimension-two case: the unit targets of X and 1-2X are distinct.
        require(F(1, x) != F(-2, 1-2*x), 'two distinct logarithmic derivatives')


def degeneracy_controls():
    p = 31
    for B in range(1, p):
        for C in range(1, p):
            exceptional = {B, (1-C) % p}
            if B != C:
                exceptional.add(B*pow(B-C, -1, p) % p)
            for q in range(2, p):
                D = (q*(q-1)+(1-q)*B+q*C) % p
                if D == 0:
                    continue
                u = B*pow(q, -1, p) % p
                v = C*pow(1-q, -1, p) % p
                w = -D*pow(q*(1-q), -1, p) % p
                require((u+v+w) % p == 1, 'branch equation')
                degenerates = any(z % p == 0 for z in (u+v, u+w, v+w))
                require(degenerates == (q in exceptional), 'three exceptional trace values')


def main():
    wronskian_controls()
    degeneracy_controls()
    d = N//4-1
    t = 2*d-2_000_000
    require(50_000*t+1 == 26_743_545_500_001 and 1000*N < 50_000*t,
            'characteristic for interpolation, contact, and independence')
    verify(2_000_000, False, weightwise=True, rational_midpoint=True, four_term=True)


if __name__ == '__main__':
    main()
