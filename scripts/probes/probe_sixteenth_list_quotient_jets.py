#!/usr/bin/env python3
"""Exact source, local quotient, incidence variance and candidate-count certificates."""
from fractions import Fraction
from math import isqrt

from probe_quarter_coset_lists import require


N = 2**30
D = N//16-1
DELTA = 225_000
T = N//4-DELTA
WORD_FLOOR = N-1_000
LINEAR_CUTOFF = 9*N//16-15


def source(weight, derivative_degree):
    """Monomials of strictly smaller weight in X,Y,V, with V-degree capped."""
    count = 0
    for k in range(derivative_degree+1):
        height = weight-(D-1)*k
        if height <= 0:
            break
        terms = (height+D-1)//D
        count += terms*height-D*terms*(terms-1)//2
    return count


def local(order, derivative_degree):
    """Rank of universal local conditions in a polynomial of bounded V-degree."""
    if order <= 0:
        return 0
    savings = sum((2*b+1-order)*(b+derivative_degree+1-order)
                  for b in range(max(0,(order+1)//2,order-derivative_degree),order))
    return (derivative_degree+1)*order*(order+1)//2-savings


def upper_sqrt(value, scale=10**9):
    scaled = value*scale**2
    return Fraction(isqrt(scaled.numerator//scaled.denominator)+1,scale)


def verify():
    primary = 5*T
    require(source(primary,2)>N*local(5,2), 'primary contact interpolant')
    total_degree = (primary-1)//(D-1)
    require(total_degree<20 and N-2*total_degree**2-2*total_degree>WORD_FLOOR,
            'large factor after exceptional sections')
    s = Fraction(T,N)
    rate = Fraction(D,N)
    stdev = upper_sqrt(rate-s*s+(s-rate)/WORD_FLOOR)
    order = 2_500
    results = {}
    for v, cap, low in [(1,1_975,LINEAR_CUTOFF),(2,625,2*(D-1))]:
        high = primary-1
        local_increment = local(order,cap-v)-local(order-1,cap-v)
        require(all(local(order-j,cap-v)-local(order-j-1,cap-v)<=local_increment
                    for j in range(total_degree+v+1)), 'bounded local increments')
        margins = []
        for weight in (low,high):
            max_order = Fraction(weight,D)+v
            avg = 1+Fraction(weight-D+1,T)+max_order*stdev/(2*s)
            margin = (source(order*T,cap)-source(order*T-weight,cap-v)
                      -N*(local(order,cap)-local(order,cap-v)+local_increment*avg))
            margins.append(margin.numerator//margin.denominator)
        require(min(margins)>0, f'positive quotient surplus for V-degree {v}')
        secondary_degree = (order*T-1)//(D-1)
        require(total_degree*secondary_degree<WORD_FLOOR, 'generic Bezout')
        results[v] = margins
    linear_word_cap = 2*(LINEAR_CUTOFF-D+1)+(LINEAR_CUTOFF//D)-1
    require(linear_word_cap>WORD_FLOOR and
            2*linear_word_cap+total_degree<2*N+1, 'two linear factors fit budget')
    require((N-D)//(T-D)<WORD_FLOOR, 'integral-family incidence')
    print(f'{N-T:,} safe errors. Primary surplus {source(primary,2)-N*local(5,2):,}.')
    print(f'Endpoint quotient surpluses {results}; isolated linear cap {linear_word_cap:,}.')


if __name__ == '__main__':
    verify()
