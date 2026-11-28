#!/usr/bin/env python3
"""Adaptive and exterior-word certificates for four named low-rate budgets."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import adaptive_interval, linear
from probe_linear_contact_quotient import N, slots, rank, require, upper_sqrt


def curve_bound(b,v,d,t):
    return (2*b*v-v*v+b+d*(4*b*v-2*b-2*v*v)+F(v*(N-d),t-d))


def ordinary_budget(rate,budget,agreement,order,stock,linear_cutoff,rows):
    t = (agreement*N).__ceil__()
    d = N//rate-1
    P = order*t
    b = (P-1)//(d-1)
    require(slots(P,4,d)>N*rank(order,4),'quartic primary')
    require(4*stock+b<=budget,'no large components')
    for v,h,lam,b2,j2,c,r in rows:
        adaptive_interval(v,h,lam,b2,j2,d,t,b,stock,r,80,(c*(d-1),P-1))
        if c>v:
            require(curve_bound(c-1,v,d,t)+(4-v)*stock+b<=budget,'residual product budget')
    require(stock>b*((3000*t-1)//(d-1)),'ordinary linear Bezout')
    linear(d,t,P,b,linear_cutoff,False)
    degree = linear_cutoff-1
    population = max(degree+(2*degree-2)*d,F(N-d,t-d))
    require(population+3*stock+b<=budget,'residual linear budget')
    return N-t


def first_eighth():
    agreement = F(343,1000)
    t = (N*agreement).__ceil__()
    d = N//8-1
    P = 8*t
    b = (P-1)//(d-1)
    stock = N//40
    require(slots(P,3,d)-N*rank(8,3)==8_591_214,'first eighth primary')
    for v,h,lam,b2,j2 in ((2,500,4999,'6.4','.25'),(3,600,4857,'9','.35')):
        adaptive_interval(v,h,lam,b2,j2,d,t,b,stock,2000,80,(3*(d-1),P-1))
    require(curve_bound(2,2,d,t)+stock+b<=N and 3*stock+b<=N,'derivative-quadratic group')
    require(stock>b*((3000*t-1)//(d-1)) and linear(d,t,P,b,7,False)>0,
            'top linear weights')
    def order_floor(w,r,h):
        gain = slots(r*t,h,d)-slots(r*t-w,h-1,d)
        return F(gain-N*(rank(r,h)-rank(r,h-1)),N*(rank(r,h-1)-rank(r-1,h-1)))
    r,h = 12_000,6000
    require(stock>(r*t-1)//d+5*h,'quartic discriminant Bezout')
    require(all(order_floor(w,r,h)>F(3,2)+F(6*(w-d+1)-12*d,2*N)
                for w in (5*d-1,6*d-2)),'squarefree quartic denominator')
    require(max(5+7*d,F(N-d,t-d))+2*stock+b<=N,'degree-five residuals')
    J = F(53,1000)
    R = F(d,N)
    ext = 1000
    group = N-ext
    sd = upper_sqrt((J+F(1,4))*(R-agreement**2+(agreement-R)/ext))
    lo,hi = 6*d-1,7*d-2
    cuts = [lo+(hi-lo)*i//32 for i in range(33)]
    for x,y in zip(cuts,cuts[1:]):
        for cap in range(1000,20001,1000):
            require(stock>(20000*t-1)//d+6*cap,'degree-six mixed Bezout')
            zs = [order_floor(w,20000,cap) for w in (x,y)]
            js = [F(5*w+6*(w-d+1)-30*d,N)+7-4*z for w,z in zip((x,y),zs)]
            if max(js)<0 or (max(js)<=J and
                              all(agreement*z-F(w,N)>sd for w,z in zip((x,y),zs))):
                break
        else:
            raise AssertionError('degree-six excess classes and exterior words')
    mu = upper_sqrt(R+F(1,group))
    eta = R-agreement**2+(1+J)/group
    dim = int(N*(1-(1-mu)**5+F(10,group)+5*upper_sqrt(J*eta)))+6
    nullity = group-dim
    m = (group-1)//(nullity-1)
    require((dim,nullity,m)==(1_058_494_473,15_246_351,70),'degree-six cofactor rank')
    require(6*d*group**2<2**157 and nullity+1>2*m+5+12*m*6,'tame split-fiber count')
    require(t>F(N,group)+F(group-1,group-2)*d,'Riccati sections')
    return N-t


def verify():
    eighth_second = ordinary_budget(8,2*N,F(17,50),9,N//16,7,[
        (2,2500,25500,'6.504','.18',4,10000),
        (3,3000,25000,'9.38','.22',3,10000),
        (4,3000,25000,'12.508','.22',4,10000),
    ])
    sixteenth_first = ordinary_budget(16,N,F(19,80),8,N//13,8,[
        (2,3000,35500,'12.606','.473',4,10000),
        (3,1750,17250,'17.88','.635',4,5000),
        (4,1750,17250,'23.84','.635',4,5000),
    ])
    sixteenth_second = ordinary_budget(16,2*N,F(237,1000),8,N//9,8,[
        (2,3500,35000,'12.253','.597',7,10000),
        (3,1750,17250,'17.88','.65',5,5000),
        (4,1750,17250,'23.84','.65',4,5000),
    ])
    actual = first_eighth(),eighth_second,sixteenth_first,sixteenth_second
    require(actual==(705_448_378,708_669_603,818_728_140,819_265_011),'closed endpoints')
    print(f'Closed safe counts, first and second eighth rate: {actual[0]:,}, {actual[1]:,}.')
    print(f'Closed safe counts, first and second sixteenth rate: {actual[2]:,}, {actual[3]:,}.')


if __name__ == '__main__':
    verify()
