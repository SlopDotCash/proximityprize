#!/usr/bin/env python3
"""Half-rate list safety on the second named field at 701/1000 agreement."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import adaptive_interval
from probe_linear_contact_quotient import N, slots, rank, require, upper_sqrt


AGREEMENT = F(701,1000)
T = (AGREEMENT*N).__ceil__()
D = N//2-1
P = 16*T
DEGREE = (P-1)//(D-1)
STOCK = N//64
GROUP = 2*N-4*STOCK-DEGREE


def order_floor(weight,v,order,cap):
    gain = slots(order*T,cap,D)-slots(order*T-weight,cap-v,D)
    reserved = N*(rank(order,cap)-rank(order,cap-v))
    jump = rank(order,cap-v)-rank(order-1,cap-v)
    return F(gain-reserved,N*jump)


def products():
    require(slots(P,4,D)-N*rank(16,4)==193_275_615,'quartic primary')
    rows = [
        (2,2000,13000,'1.692','.053',15*D//2,17*D//2),
        (2,2500,12500,'1.564','.037',17*D//2,19*D//2),
        (2,3000,12000,'1.442','.074',19*D//2,21*D//2),
        (2,4000,11500,'1.324','.090',21*D//2,12*D),
        (2,5500,11000,'.899','.401',12*D,P-1),
        (3,1500,13000,'2.537','.045',3*(D-1),P-1),
        (4,2000,13000,'3.383','.051',4*(D-1),P-1),
    ]
    for v,h,lam,b2,j2,lo,hi in rows:
        adaptive_interval(v,h,lam,b2,j2,D,T,DEGREE,STOCK,10_000,80,(lo,hi))
    require(STOCK-DEGREE**2>DEGREE*((6000*T-1)//D),'ordinary quadratic Bezout')
    for a in range(6):
        bounds = ((2+a)*D-2,min((3+a)*D-3,15*D//2))
        require(any(all(order_floor(w,2,6000,h)>a+F(2*(w-2*(D-1)-a*D),N) for w in bounds)
                    for h in range(300,6000,300)),'low quadratic weights')


def linear_factors():
    require(max(2+2*D,F(N-D,T-D))+4*STOCK+DEGREE<=2*N,'linear factors of degree at most two')
    order = 20_000
    caps = [order*i//12 for i in range(1,13)]
    require(GROUP>(order*T-1)//D+DEGREE*max(caps),'linear mixed Bezout')
    limits = {3:F(9,10),4:F(1),5:F(63,100),6:F(15,100)}
    mu = upper_sqrt(F(D,N)+F(1,GROUP))
    dimensions = []
    for b in range(3,DEGREE+1):
        lo,hi = b*D-1,min(P-1,(b+1)*D-2)
        if lo>hi:
            continue
        limit = limits.get(b,0)
        def plane(w):
            return F((b-1)*w+b*(w-D+1)-b*(b-1)*D,N)
        cuts = [lo+(hi-lo)*i//16 for i in range(17)]
        for x,y in zip(cuts,cuts[1:]):
            orders = [(order_floor(x,1,order,h),order_floor(y,1,order,h)) for h in caps]
            bound = min(max(plane(w)+j*(j+1)+1-2*j*z for w,z in zip((x,y),zs))
                        for j in range(2,b+2) for zs in orders)
            require(bound<=limit if limit else bound<0,'collision classes or weight exclusion')
        if not limit:
            continue
        r = b-1
        eta = F(D,N)-AGREEMENT**2+(1+limit)/GROUP
        union = 1-(1-mu)**r+F(r*(r-1),2*GROUP)
        dim = int(N*(union+r*upper_sqrt(limit*eta)))+r+1
        require((GROUP-1)//(GROUP-dim-1)<=2,'quadratic first integral')
        dimensions.append(dim)
    require(6*D*GROUP**2<2**157 and GROUP-max(dimensions)>21,'tame quadratic splitting')
    require(N*T>0 and T>F(N,GROUP)+F(GROUP-1,GROUP-2)*D,'Riccati count')
    require(N-T==321_048_805,'integer conversion')
    return dimensions


if __name__=='__main__':
    products()
    dims = linear_factors()
    print(f'Second named half-rate budget safe through {N-T:,} errors at {AGREEMENT} agreement.')
    print(f'{GROUP:,} sections; cofactor dimension caps {dims}; first-integral degree at most two.')
