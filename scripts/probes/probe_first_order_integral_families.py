#!/usr/bin/env python3
"""Check the first-order slot counts, plane-curve degree bounds and prime examples."""
from fractions import Fraction
from math import comb

from probe_quarter_coset_lists import require


def row_cost(order, v):
    # Each block has min(order-i, number of terms) possible independent Taylor rows.
    direct = sum(min(order-i, min(i, j)-max(0, j-v)+1)
                 for i in range(order) for j in range(i+v+1))
    closed = ((v+1)*comb(order+1, 2)
              - sum(max(0, 2*i+1-order)*max(0, i+v+1-order) for i in range(order)))
    require(direct == closed, 'radial rank formula')
    return direct


def cap(b, v, d):
    return 2*b*v-v*v + d*(4*b*v-b-2*v*v-v)


def verify_production():
    n = 2**30
    # rate denominator, errors / (n/4096), order, total/derivative degree,
    # budget coefficient, prime offset in units of 2**100, primality witness.
    cases = [(2, 1215, 13, 18, 3, 89, 4, 11), (4, 2089, 12, 23, 3, 59, 10, 5),
             (8, 2695, 10, 27, 3, 35, 11, 3), (16, 3116, 7, 25, 4, 22, 89, 5)]
    for q, errors, order, b, v, budget, offset, witness in cases:
        e = errors*(n//4096)
        t, d = n-e, n//q-1
        slots = sum(max(0, order*t-d*j-(d-1)*k)
                    for k in range(v+1) for j in range(b-k+1))
        surplus = slots-n*row_cost(order, v)
        charge = cap(b, v, d)+b+Fraction(b*v*(n-d), t-d)
        p = budget*2**158+offset*2**100+1
        require(surplus>0 and charge <= budget*n, 'finite slot and list comparisons')
        require(order*t+1 < p and b < p, 'Taylor truncation and separability')
        require(p//2**128 == budget*n and (p-1) % 2**100 == 0, 'literal budget and order')
        require(pow(witness, (p-1)//2, p) == p-1 and (2**100+1)**2 > p, 'prime certificate')
        generator = pow(witness, (p-1)//n, p)
        require(pow(generator, n//2, p) == p-1, 'order of smooth grid generator')
        print(f'1/{q}: {e:,} errors, surplus {surplus:,}, cap {int(charge):,}, '
              f'budget {budget}n on p={p}')


def check_degrees():
    for b in range(1, 21):
        for v in range(1, b+1):
            for d in range(1, 11):
                total, ordinate = 1+2*d*(b-1), 1+d*(2*v-1)
                singular = v*(b-1)+(b-v)*(v-1)
                require(singular+v*total+(b-v)*ordinate == cap(b, v, d),
                        'intersection calculation')
                for a in range(1, b):
                    for w in range(1, min(a+1, v)):
                        if v-w<=b-a:
                            require(cap(a,w,d)+cap(b-a,v-w,d)<=cap(b,v,d),
                                    'sum over irreducible factors')
    # A polynomial family with two generic points above an ordinate.
    # f_c(X)=c^2+Xc. Its jets satisfy V^2+XV-Y=0. A fiber can be double
    # at a branch point. The incidence bound must count distinct parameters.
    p, grid = 31, range(12)
    for shift in range(p):
        center = [(x*x+shift)%p for x in grid]
        hits = [sum((c*c+x*c)%p == y for x,y in zip(grid, center)) for c in range(p)]
        require(sum(hits)<=2*len(grid), 'quadratic integral family incidences')


if __name__ == '__main__':
    verify_production()
    check_degrees()
