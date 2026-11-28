#!/usr/bin/env python3
"""Exact common-occupancy and variance-bin certificates at the second sixteenth rate."""
from fractions import Fraction as F

from probe_quarter_coset_lists import require
from probe_sixteenth_list_adaptive_quotient import rank
from probe_sixteenth_list_quotient_jets import N, D, source


def certificate():
    t = N//4-13_000_000
    s = F(t,N)
    primary = 8*t
    b = (primary-1)//(D-1)
    stock = N//25
    m0 = stock-b*b
    vmax = F(D,N)-s*s+(s-F(D,N))/m0
    require(source(primary,4)>N*rank(8,4) and b<32, 'fourth-degree primary')
    r = 5000
    bins = 32
    results = {}
    rows = [(1,4500,17265,F(45,10),F(15,10),16),
            (2,1750,17344,F(121,10),F(7,10),7),
            (3,1750,17346,F(181,10),F(7,10),5),
            (4,1750,17348,F(241,10),F(7,10),4)]
    for v,h,lam,b2,j2,low_factor in rows:
        def base(q):
            return rank(q,h)-rank(q,h-v)

        def inc(q):
            return rank(q,h-v)-rank(q-1,h-v)

        rb = F(base(r+10)-base(r-10),20)
        linear = F(inc(r),s)
        first = (r-lam*s).__floor__()
        last = (r+lam*(1-s)).__floor__()
        require(first>0 and rb>0, 'positive multiplicity parameters')
        for q in range(first,last+1):
            x = q-r
            distance = min(abs(x),abs(x+1))
            square = F(r*distance,lam)**2
            require(base(q)<=base(r)+rb*x+F(r,2)+b2*square, 'base local cost')
            require(inc(q)<=inc(r)+linear*F(x,lam)+F(r,2)+j2*square, 'occupancy-weighted increment')
        # Average minus the integral weight cutoff is at least 2t on every
        # group. Using zero variance for the denominator only increases it.
        eligible = m0*2*t/(3*t+1+lam*N*vmax)
        max_weight = ((r-3)*t+lam*N*vmax).__floor__()
        mixed_bezout = v*((max_weight-1)//D)+h*b
        require(eligible>mixed_bezout, 'enough eligible words on each large component')
        worst = None
        for idx in range(bins):
            low_variance = vmax*F(idx,bins)
            high_variance = vmax*F(idx+1,bins)
            wt = ((r-3)*t+lam*N*low_variance).__floor__()
            for weight in (low_factor*(D-1),primary-1):
                local_cost = (base(r)+F(r,2)+b2*r*r*high_variance
                              +linear*(s+F(weight-D+1,N))
                              +(F(r,2)+j2*r*r*high_variance)*(F(weight,D)+v))
                margin = source(wt,h)-source(wt-weight,h-v)-N*local_cost
                score = margin.__floor__()
                worst = score if worst is None else min(worst,score)
        require(worst>0, 'all variance intervals and weight endpoints have surplus')
        results[v] = (worst, eligible.__floor__(), mixed_bezout)
        if low_factor>v:
            size = low_factor-1
            normalized = (2*size*v-v*v+size+D*(4*size*v-2*size-2*v*v)
                          +v*F(N-D,t-D))
            require(normalized+4*stock+b<2*N+1, 'total small and large factor budget')
    require(4*stock+b<2*N+1, 'all groups small')
    print(f'{N-t:,} safe errors; primary surplus {source(primary,4)-N*rank(8,4):,}.')
    print(f'(Worst quotient surplus, eligible group size, mixed Bezout) by derivative degree: {results}')


if __name__=='__main__':
    certificate()
