#!/usr/bin/env python3
"""Certify quotient interpolation for named list budgets using plane intersections."""
from fractions import Fraction
from functools import cache
from math import isqrt

from probe_quarter_coset_lists import require
from probe_sixteenth_list_quotient_jets import upper_sqrt
from probe_sixteenth_list_adaptive_quotient import rank

N = 2**30
ORDER = 6000


@cache
def slots(weight, cap, d):
    total = 0
    for power in range(cap+1):
        room = weight-(d-1)*power
        if room <= 0:
            break
        height = (room+d-1)//d
        total += height*room-d*height*(height-1)//2
    return total


def certify(rate, extra, primary_order, quadratic_cap):
    d = N//rate-1
    t = isqrt(N*d)-extra
    primary = primary_order*t
    degree = (primary-1)//(d-1)
    spare = slots(primary,2,d)-N*rank(primary_order,2)
    require(spare > slots(primary-17*d+2,0,d), 'seven exterior words')
    threshold = N//8 if rate == 8 else N//4
    retained = threshold-degree**2
    require(retained > degree*((ORDER*t-1)//(d-1)), 'secondary Bezout bound')
    s = Fraction(t,N)
    sigma = upper_sqrt(Fraction(d,N)-s*s+(s-Fraction(d,N))/retained)

    def margin(weight, v, cap, mean):
        source = slots(ORDER*t,cap,d)-slots(ORDER*t-weight,cap-v,d)
        jump = rank(ORDER,cap-v)-rank(ORDER-1,cap-v)
        return source-N*(rank(ORDER,cap)-rank(ORDER,cap-v)+jump*mean)

    for w in (2*(d-1),primary-1):
        mean = 1+Fraction(w-d+1,t)+(Fraction(w,d)+2)*sigma/(2*s)
        require(margin(w,2,quadratic_cap,mean)>0, 'quadratic quotient')

    low,high = (5 if rate == 8 else 6)*d-1,primary-1
    cuts = {low,high+1}
    for j in range(low//d,high//d+2):
        cuts.update(w for w in (j*d-1,j*d) if low<w<=high)
    cuts = sorted(cuts)
    least_margin = None
    for start,stop in zip(cuts,cuts[1:]):
        a, b = (start-d+1)//d, start//d
        best = None
        for k in range(2,b+2):
            def mean(w):
                intersection = a*w+b*(w-d+1)-d*a*b
                return Fraction(k*(k+1)+1,2*k)+Fraction(intersection,2*k*N)
            for percentage in (25,30,35,45,55,65,75,85):
                cap = ORDER*percentage//100
                surplus = min(margin(w,1,cap,mean(w)) for w in (start,stop-1))
                if best is None or surplus>best:
                    best = surplus
        require(best>0, f'linear quotient at weights {start:,} through {stop-1:,}, margin {best}')
        least_margin = best if least_margin is None else min(least_margin,best)

    group_cap = 5+8*d
    budget = 16*N//rate
    require(2*group_cap+6==budget and (N-d)//(t-d)<threshold, 'small-degree groups')
    require(group_cap+max(threshold,4+6*d)+degree<=budget, 'one smaller group')
    if rate == 8:
        require(4+6*d+threshold+degree < N, 'unique large linear factor at first prime')
    print(f'1/{rate}: {N-t:,} safe errors at budget {N:,}; primary surplus {spare:,}, '
          f'least linear surplus {least_margin.__floor__():,}.')


if __name__ == '__main__':
    certify(16,750_000,5,1800)
    certify(8,1_000_000,6,1800)
