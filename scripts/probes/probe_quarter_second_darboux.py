#!/usr/bin/env python3
"""Verify the second named quarter-rate budget at the order-twelve primary pivot."""

from fractions import Fraction as F

from probe_joint_list_contact_boards import BOARDS, adaptive, linear
from probe_linear_contact_quotient import N, rank, require, slots, upper_sqrt


D = N//4-1
ERRORS = 547_807_172
T = N-ERRORS
S = F(T,N)
PRIMARY = 12*T
DEGREE = (PRIMARY-1)//(D-1)
STOCK = N//40
GROUP = 2*N-3*STOCK-DEGREE
ORDER = 20_000


def order_bound(weight, cap):
    gain = slots(ORDER*T,cap,D)-slots(ORDER*T-weight,cap-1,D)
    quota = N*(rank(ORDER,cap)-rank(ORDER,cap-1))
    jump = rank(ORDER,cap-1)-rank(ORDER-1,cap-1)
    return F(gain-quota,jump*N)


def verify():
    primary_surplus = slots(PRIMARY,3,D)-N*rank(12,3)
    require(primary_surplus==494,'primary interpolation')
    products = [adaptive(v,h,lam,b2,j2,v,D,T,PRIMARY,DEGREE,STOCK)
                for v,h,lam,b2,j2,_ in BOARDS[-1][-1]]
    require(products==[9_378_269_995,207_607_765_007_531],'joint product bounds')
    require(STOCK>DEGREE*((3000*T-1)//(D-1)),'ordinary secondary Bezout')
    require(linear(D,T,PRIMARY,DEGREE,6,False)>0,'weights at least 6d-1')
    require(max(4+6*D,F(N-D,T-D))+3*STOCK+DEGREE<=2*N,'small total degree')
    J = F(1,2)
    left,right = 5*(D-1),6*D-2
    cuts = sorted({left,right,*(left+(right-left)*i//32 for i in range(1,32))})
    for x,y in zip(cuts,cuts[1:]):
        def plane(w):
            return F(4*w+5*(w-D+1)-20*D,N)
        require(any(GROUP>(ORDER*T-1)//D+5*h and
                    all(plane(w)+offset-lam*order_bound(w,h)<=J for w in (x,y))
                    for lam,offset in ((4,7),(6,13))
                    for h in (8000,9000,10000,11000,12000,13000,14000)),
                'excess collision classes')
    mu = upper_sqrt(F(D,N)+F(1,GROUP))
    eta = F(D,N)-S**2+(1+J)/GROUP
    union = 1-(1-mu)**4+F(6,GROUP)
    dimension = int(N*(union+4*upper_sqrt(J*eta)))+5
    nullity = GROUP-dimension
    m = (GROUP-1)//(nullity-1)
    require(m<=2 and 2*m-2<3,'first-integral pole bound')
    require(6*D*GROUP**2<2**157,'separable differential descent')
    print(f'Safe through {ERRORS:,} errors at the second named budget {2*N:,}.')
    print(f'Primary surplus {primary_surplus}; joint surpluses {products}.')
    print(f'{GROUP:,} sections, cofactor rank at most {dimension:,}, nullity at least {nullity:,}.')
    print(f'First-integral degree at most {m}, giving at most {2*m-2} poles with multiplicity.')


if __name__=='__main__':
    verify()
