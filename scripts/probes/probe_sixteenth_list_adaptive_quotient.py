#!/usr/bin/env python3
"""Certify the second jet interpolation with site-dependent contact multiplicities."""
from fractions import Fraction as F

from probe_quarter_coset_lists import require
from probe_sixteenth_list_quotient_jets import N, D, LINEAR_CUTOFF, WORD_FLOOR, source


def rank(order, cap):
    if order <= 0:
        return 0
    a = min(order//2,cap)
    savings = (a*(order-1)*cap-(order-1+2*cap)*a*(a-1)//2
               +a*(a-1)*(2*a-1)//3)
    return (cap+1)*order*(order+1)//2-savings


def certificate():
    t = N//4-5_100_000
    s = F(t,N)
    variance = F(D,N)-s*s+(s-F(D,N))/WORD_FLOOR
    primary = 7*t
    total_degree = (primary-1)//(D-1)
    require(source(primary,2)>N*rank(7,2) and N-100-total_degree**2>WORD_FLOOR,
            'primary jet interpolation and regular group')
    cap_linear = 2*(LINEAR_CUTOFF-D+1)+LINEAR_CUTOFF//D-1
    require(2*cap_linear+total_degree<2*N+1, 'two linear groups')
    r = 5_000
    wt = (r-2)*t
    results = {}
    for v,h,lam,b2,j2,low in [(1,4400,16694,F(42,10),F(14,10),LINEAR_CUTOFF),
                              (2,1400,17537,F(124,10),F(4,10),2*(D-1))]:
        def base(q):
            return rank(q,h)-rank(q,h-v)

        def inc(q):
            return rank(q,h-v)-rank(q-1,h-v)

        rb = F(base(r+10)-base(r-10),20)
        length = F(inc(r),s)
        first = (r-lam*s).__floor__()
        last = (r+lam*(1-s)).__floor__()
        require(first>0 and rb>0, 'positive lengths')
        for q in range(first,last+1):
            x = q-r
            m = min(abs(x),abs(x+1))
            square = F(r*m,lam)**2
            require(base(q)<=base(r)+rb*x+F(r,2)+b2*square, 'base local cost')
            require(inc(q)<=inc(r)+length*F(x,lam)+F(r,2)+j2*square, 'weighted local increment')
        zeros_floor = WORD_FLOOR*t/(2*t+lam*N*variance)
        require(zeros_floor>total_degree*((wt-1)//(D-1)), 'enough long sections for Bezout')
        margins = []
        for weight in (low,primary-1):
            order_cap = F(weight,D)+v
            local_cost = (base(r)+F(r,2)+b2*r*r*variance
                          +length*(s+F(weight-D+1,N))
                          +(F(r,2)+j2*r*r*variance)*order_cap)
            margin = source(wt,h)-source(wt-weight,h-v)-N*local_cost
            margins.append(margin.__floor__())
        require(min(margins)>0, 'positive secondary quotient surplus')
        results[v] = margins
    print(f'{N-t:,} safe errors; primary surplus {source(primary,2)-N*rank(7,2):,}.')
    print(f'Secondary endpoint surpluses {results}.')


if __name__ == '__main__':
    certificate()
