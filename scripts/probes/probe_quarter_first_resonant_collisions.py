#!/usr/bin/env python3
"""First-prime quarter-rate list safety at 9939/20000 agreement."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import linear
from probe_linear_contact_quotient import N, rank, require, upper_sqrt
from probe_quarter_second_quartic_darboux import B, D, P, STOCK, T, products
from probe_quarter_uniform_four_term import intersection, intervals, mean_order, source


S = F(9939,20000)
R = F(1,4)
PRELIMINARY = N-4*STOCK-B
GROUP = N-1000


def order_floor(w, order, cap, agreement=S):
    gain = source(order*agreement,cap)-source(order*agreement-w,cap-1)
    return (gain-rank(order,cap)+rank(order,cap-1))/(rank(order,cap-1)-rank(order-1,cap-1))


def initial_band(agreement=S):
    products()
    require(STOCK>B*((3000*T-1)//(D-1)) and linear(D,T,P,B,6,False)>0,
            'positive derivative product and upper linear weight')
    nonradial = 7*(1-agreement*agreement/(R+(2*agreement-R)/PRELIMINARY))
    require(1-nonradial>3*R and PRELIMINARY>5*int(6000*agreement/R), 'low-degree prerequisites')
    for b in range(1,5):
        for a in range(b):
            lo = max(agreement+2*R-nonradial,b*R,4*R if a==0 else 0)
            for x,y in intervals(lo,(b+1)*R,[4*R+R/4,4*R+R/2]):
                if a in (2,3):
                    require(y-R-a*R<1-nonradial, 'repeated denominator content')
                def upper(w,j):
                    if j>0:
                        return mean_order(w,a,b,j)
                    e = w-R
                    if j<0:
                        return 1+2*e-2*R
                    if a==3:
                        return (3+4*e-6*R)/2
                    if a==2:
                        return 2+(e-2*R)/3+(intersection(w,a,b)-1)/6
                    return 1+2*(e-R) if a==1 else 1+e
                tests = (-1,0,2,3,4,5) if a==2 else (0,2,3,4,5)
                require(any(all(order_floor(w,6000,h,agreement)>upper(w,j) for w in (x,y))
                            for j in tests for h in range(300,6000,300)), 'lower linear weights')


def degree_five():
    excess = F(131,1000)
    delta = upper_sqrt((excess+F(1,4))*(R-S*S+(S-R)/1000))
    cuts = [5*R+R*i/80 for i in range(81)]
    require(PRELIMINARY>int(50000*S/R)+5*32000, 'large quotient Bezout')
    for ends in zip(cuts,cuts[1:]):
        options = [(h,slope,bias) for h in range(20000,32001,1000) for slope,bias in ((4,7),(6,13))]
        for h,slope,bias in options:
            orders = [order_floor(w,50000,h) for w in ends]
            costs = [intersection(w,4,5)+bias-slope*z for w,z in zip(ends,orders)]
            if max(costs)<0 or (max(costs)<=excess and all(S*z-w>delta for w,z in zip(ends,orders))):
                break
        else:
            raise AssertionError('degree-five exterior words or exceptional classes')
    price,moment,q = F(299,1000), F(798,100), F(151,1000)
    slope = 4*(1-q)**3
    offset = 1-(1-q)**4-q*slope
    require(price>=offset+slope**2/(4*moment) and 12*price*moment>=16,'two class bounds')
    require(4*(1-S)**3<=2*moment*S, 'decreasing coupled rank')
    eta = R-S*S+(1+excess)/GROUP
    sampling = F(6,GROUP)*(1+excess)+F(4,GROUP)*excess
    dim = int(N*(1-(1-S)**4+price*excess+moment*eta+sampling))+5
    nullity = GROUP-dim
    require(nullity>1, 'positive cofactor nullity')
    m = (GROUP-1)//(nullity-1)
    split = 2*m+5+12*m*5
    require((dim,nullity,m,split)==(1_073_091_968,648_856,1654,102_553), 'split fiber data')
    require(nullity+1>split and 6*D*GROUP**2<2**157 and D**2<2**157, 'characteristic and tame cover')
    require(S*N>F(N,GROUP)+F(GROUP-1,GROUP-2)*D, 'Riccati count')


if __name__=='__main__':
    initial_band()
    degree_five()
    errors = int(N*(1-S))
    require(errors==540_145_824, 'closed endpoint')
    print(f'First-prime quarter-rate list budget is safe through {errors:,} errors.')
