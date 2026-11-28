#!/usr/bin/env python3
"""First-prime eighth-rate list safety by individual exterior hits and coupled cofactor counts."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import adaptive_interval, linear
from probe_linear_contact_quotient import N, rank, require, slots, upper_sqrt
from probe_low_rate_named_adaptive_cofactors import curve_bound


AGREEMENT = F(137, 400)
T = (AGREEMENT*N).__ceil__()
D = N//8 - 1
PRIMARY = 9*T
DEGREE = (PRIMARY-1)//(D-1)
STOCK = N//25


def order_floor(weight, order, cap):
    gain = slots(order*T, cap, D) - slots(order*T-weight, cap-1, D)
    base = rank(order, cap) - rank(order, cap-1)
    jump = rank(order, cap-1) - rank(order-1, cap-1)
    return F(gain-N*base, N*jump)


def large_products():
    require(slots(PRIMARY, 4, D) > N*rank(9, 4), 'quartic primary')
    rows = [(2, 500, 4999, '6.255', '.204'),
            (3, 600, 4857, '8.861', '.280'),
            (4, 600, 5000, '12.527', '.205')]
    for v, cap, slope, base, jump in rows:
        adaptive_interval(v, cap, slope, base, jump, D, T, DEGREE, STOCK, 2000, 80,
                          (max(3,v)*(D-1), PRIMARY-1))
    require(curve_bound(2, 2, D, T) + 2*STOCK + DEGREE <= N and 4*STOCK + DEGREE <= N,
            'small-only and quadratic groups')
    require(STOCK > DEGREE*((3000*T-1)//(D-1)) and linear(D,T,PRIMARY,DEGREE,7,False)>0,
            'linear weights above degree six')


def individual_exterior():
    require(STOCK > (12000*T-1)//D + 5*12000, 'quartic mixed Bezout')
    lo, hi = 5*D-1, 6*D-2
    cuts = [lo+(hi-lo)*i//64 for i in range(65)]
    for x, y in zip(cuts, cuts[1:]):
        for cap in range(3000, 12001, 750):
            ends = (x, y)
            slack = [F(3,2)+F(6*(w-D+1)-12*D,2*N)-order_floor(w,12000,cap) for w in ends]
            if max(slack)<0 or all(2*AGREEMENT-2*e>F(w,N) for w,e in zip(ends,slack)):
                break
        else:
            raise AssertionError('quartic individual exterior word')
    require(max(5+8*D, F(N-D,T-D)) <= N, 'squarefree quartic population')
    require(max(5+7*D, F(N-D,T-D)) + 3*STOCK + DEGREE <= N, 'other degree-five factors')


def coupled_rank():
    excess = F(77,1000)
    rate = F(D,N)
    exterior = 1000
    group = N-exterior
    deviation = upper_sqrt((excess+F(1,4))*(rate-AGREEMENT**2+(AGREEMENT-rate)/exterior))
    lo, hi = 6*D-1, 7*D-2
    cuts = [lo+(hi-lo)*i//32 for i in range(33)]
    require(STOCK > (20000*T-1)//D + 6*20000, 'sextic mixed Bezout')
    for x,y in zip(cuts,cuts[1:]):
        for cap in range(1000, 20001, 1000):
            ends = (x,y)
            orders = [order_floor(w,20000,cap) for w in ends]
            costs = [F(5*w+6*(w-D+1)-30*D,N)+7-4*z for w,z in zip(ends,orders)]
            if max(costs)<0 or (max(costs)<=excess and
                                all(AGREEMENT*z-F(w,N)>deviation for w,z in zip(ends,orders))):
                break
        else:
            raise AssertionError('degree-six exterior words and exceptional classes')
    eta = rate-AGREEMENT**2+(1+excess)/group
    require((1-AGREEMENT)**8*eta <= excess*AGREEMENT**2, 'decreasing coupled rank bound')
    dim = int(N*(1-(1-AGREEMENT)**5+F(10,group)+5*upper_sqrt(excess*eta)))+6
    nullity = group-dim
    require(nullity>1, 'positive cofactor nullity')
    m = (group-1)//(nullity-1)
    require((dim,nullity,m)==(1_072_473_701,1_267_123,847), 'primitive first integral')
    require(6*D*group**2<2**157 and nullity+1>2*m+5+12*m*6, 'tame split fibers')
    require(T > F(N,group)+F(group-1,group-2)*D, 'Riccati count')


if __name__ == '__main__':
    large_products()
    individual_exterior()
    coupled_rank()
    require(N-T==705_985_249, 'closed error count')
    print(f'First-prime eighth-rate list budget is safe through {N-T:,} errors.')
