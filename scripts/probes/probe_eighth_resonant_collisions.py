#!/usr/bin/env python3
"""First-prime eighth-rate list safety using local intersections and section contact orders."""

from fractions import Fraction as F

from probe_eighth_coupled_cofactor import D, STOCK, finish, large_products, order_floor
from probe_linear_contact_quotient import N, require, upper_sqrt


S = F(273,800)
T = (N*S).__ceil__()
GROUP = N - 1000
CASES = (
    (5,F(395,1000),F(288,1000),F(169,20),F(147,1000),(1_071_251_124,2_489_700,431)),
    (6,F(162,1000),F(516,1000),F(81,20),F(224,1000),(1_067_472_642,6_268_182,171)),
)


def quartic_individual(ends):
    for cap in range(3000,12001,750):
        slack = [F(3,2)+F(6*(w-D+1)-12*D,2*N)-order_floor(w,12000,cap,T) for w in ends]
        if max(slack)<0 or all(2*S-2*z>F(w,N) for w,z in zip(ends,slack)):
            return True
    return False


def check_weight(b, excess):
    variance = F(D,N)-S*S+(S-F(D,N))/1000
    deviation = upper_sqrt((excess+F(1,4))*variance)
    lo, hi = b*D-1, (b+1)*D-2
    cuts = [lo+(hi-lo)*i//96 for i in range(97)]
    require(STOCK>(20000*T-1)//D+b*20000, 'mixed Bezout')
    for ends in zip(cuts,cuts[1:]):
        if b==5 and quartic_individual(ends):
            continue
        plane = [F((b-1)*w+b*(w-D+1)-b*(b-1)*D,N) for w in ends]
        for cap in range(1000,20001,500):
            orders = [order_floor(w,20000,cap,T) for w in ends]
            costs = [k+7-4*z for k,z in zip(plane,orders)]
            if max(costs)<0 or (max(costs)<=excess and
                                all(S*z-F(w,N)>deviation for w,z in zip(ends,orders))):
                break
        else:
            raise AssertionError(f'degree-{b} interval beginning at {ends[0]}')


def verify():
    large_products(T, [(2,500,4999,'6.255','.277'),(3,600,4857,'8.861','.380'),
                       (4,600,5000,'12.527','.212')])
    degree = (9*T-1)//(D-1)
    require(max(5+8*D,F(N-D,T-D))<=N and
            max(5+7*D,F(N-D,T-D))+3*STOCK+degree<=N, 'quintic alternatives')
    require(D*D<2**157, 'contact orders lift from the prime field')
    for b,excess,price,moment,q,expected in CASES:
        check_weight(b,excess)
        r = b-1
        slope = r*(1-q)**(r-1)
        offset = 1-(1-q)**r-q*slope
        require(price>=offset+slope*slope/(4*moment) and 12*price*moment>=r*r,
                'the two class bounds')
        eta = F(D,N)-S*S+(1+excess)/GROUP
        require(r*(1-S)**(r-1)<=2*moment*S, 'maximum at required agreement')
        sampling = F(r*(r-1),2*GROUP)*(1+excess)+F(r,GROUP)*excess
        dim = int(N*(1-(1-S)**r+price*excess+moment*eta+sampling))+r+1
        finish(T,GROUP,dim,expected)
    require(N-T==707_327_426, 'closed endpoint')
    print(f'First-prime eighth-rate list budget is safe through {N-T:,} errors.')


if __name__=='__main__':
    verify()
