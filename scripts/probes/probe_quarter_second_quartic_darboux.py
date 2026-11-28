#!/usr/bin/env python3
"""Second named quarter-rate budget from a quartic primary and pole degrees."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import adaptive_interval, linear
from probe_linear_contact_quotient import N, slots, rank, require, upper_sqrt


D = N//4-1
AGREEMENT = F(61,125)
T = (AGREEMENT*N).__ceil__()
P = 11*T
B = (P-1)//(D-1)
STOCK = N//40
GROUP = 2*N-4*STOCK-B


def order_floor(weight, v, order, cap):
    gain = slots(order*T,cap,D)-slots(order*T-weight,cap-v,D)
    reserved = N*(rank(order,cap)-rank(order,cap-v))
    jump = rank(order,cap-v)-rank(order-1,cap-v)
    return F(gain-reserved,N*jump)


def products():
    require(slots(P,4,D)-N*rank(11,4)==590_560_315,'quartic primary')
    rows = [
        (3,500,3600,'4.868','.071',3*(D-1),P-1,2000,12),
        (4,500,3600,'6.493','.071',4*(D-1),P-1,2000,12),
        (2,2500,18000,'3.242','.073',6*D-2,7*D-2,10000,80),
        (2,3000,17500,'3.065','.104',7*D-2,8*D-2,10000,80),
        (2,3500,17000,'2.892','.142',8*D-2,12*D-2,10000,80),
        (2,1300,3200,'1.795','.351',12*D-2,P-1,2000,80),
    ]
    margins = [adaptive_interval(v,h,lam,b2,j2,D,T,B,STOCK,r,bins,(lo,hi))
               for v,h,lam,b2,j2,lo,hi,r,bins in rows]
    require(min(margins)==157_830_852_005_691,'adaptive product endpoints')
    require(STOCK-B**2>B*((6000*T-1)//D),'low quadratic product Bezout')
    for a in range(4):
        endpoints = ((2+a)*D-2,(3+a)*D-3)
        require(any(all(order_floor(w,2,6000,h)>a+F(2*(w-2*(D-1)-a*D),N)
                        for w in endpoints) for h in range(300,6000,300)),
                'leading ordinate coefficient bound')


def linear_factor():
    require(STOCK>B*((3000*T-1)//(D-1)) and linear(D,T,P,B,6,False)>0,'large linear weight')
    require(max(4+6*D,F(N-D,T-D))+4*STOCK+B<=2*N,'small-degree linear factor')
    lo,hi = 5*(D-1),6*D-2
    cuts = [lo+(hi-lo)*i//32 for i in range(33)]
    excess = F(53,100)
    for x,y in zip(cuts,cuts[1:]):
        def plane(w):
            return F(4*w+5*(w-D+1)-20*D,N)
        require(any(GROUP>(20000*T-1)//D+5*h and
                    all(plane(w)+off-lam*order_floor(w,1,20000,h)<=excess for w in (x,y))
                    for off,lam in ((7,4),(13,6)) for h in range(8000,14001,1000)),
                'exceptional collision class budget')
    mu = upper_sqrt(F(D,N)+F(1,GROUP))
    eta = F(D,N)-AGREEMENT**2+(1+excess)/GROUP
    dim = int(N*(1-(1-mu)**4+F(6,GROUP)+4*upper_sqrt(excess*eta)))+5
    nullity = GROUP-dim
    m = (GROUP-1)//(nullity-1)
    require(GROUP==2_040_109_447 and dim==1_347_093_591 and m==2,'degree-two first integral')
    require(6*D*GROUP**2<2**157 and 2*m-2<3,'separability and pole orders')
    require(N-T==549_755_813,'named endpoint')
    print(f'Second named quarter-rate budget safe through {N-T:,} errors at {AGREEMENT} agreement.')
    print(f'{GROUP:,} sections, cofactor rank at most {dim:,}, nullity at least {nullity:,}; m <= {m}.')


if __name__ == '__main__':
    products()
    linear_factor()
