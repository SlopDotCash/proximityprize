#!/usr/bin/env python3
"""A length-independent half-rate list certificate uniformly in the length."""
from fractions import Fraction as F

from probe_half_list_coefficient_derivatives import content_and_order, dual_proposal
from probe_linear_contact_quotient import rank, require
from probe_sixteenth_list_quotient_jets import upper_sqrt


AGREEMENT = F(181,256)
ORDER = 425
LARGE = 9_992
PRIMARY = 11*AGREEMENT
DEGREE = (2*PRIMARY).__floor__()
SIGMA = upper_sqrt(F(1,2)-AGREEMENT**2+(AGREEMENT-F(1,2))/(LARGE-DEGREE**2))


def source(w,h):
    # Sum (w-(j+k)/2)_+; multiply out the quadratic summand in k.
    m = (2*w).__ceil__()
    stop = min(h,m-1)
    if stop<0:
        return F(0)
    count = stop+1
    linear = stop*count//2
    quadratic = stop*count*(2*stop+1)//6
    return (m*count*(4*w-m+1)-(4*w+1)*linear+quadratic)/4


def margin(w,mean,v,h):
    return (source(ORDER*AGREEMENT,h)-source(ORDER*AGREEMENT-w,h-v)
            -(rank(ORDER,h)-rank(ORDER,h-v))
            -(rank(ORDER,h-v)-rank(ORDER-1,h-v))*mean)


def rows_limits(a,b,w):
    orders = list(range(1,b+2))
    e = w-F(1,2)
    rows = [tuple(max(0,o*o-o-1) for o in orders)]
    bounds = [a*w+b*e-F(a*b,2)]
    for j in range(a+1):
        data = [content_and_order(o,a,j) for o in orders]
        factor = 1 if j==a else AGREEMENT
        rows.append(tuple(h+factor*q for h,q in data))
        cost = e-F(j,2)
        if j<a:
            cost += SIGMA*max(q for _,q in data)/2
        bounds.append(cost)
    rows.append(tuple(orders))
    bounds.append((AGREEMENT+e+(1-AGREEMENT)*a/2+SIGMA*(b+1))/(AGREEMENT+(1-AGREEMENT)/2))
    return rows,bounds


def linear(a,b,left,right):
    mid = (left+right)/2
    rows,bounds = rows_limits(a,b,mid)
    weights,bias = dual_proposal(rows,bounds)
    def mean(w):
        return bias+sum(c*u for c,u in zip(weights,rows_limits(a,b,w)[1]))
    h = max(range(1,ORDER,max(1,ORDER//180)),key=lambda k:margin(mid,mean(mid),1,k))
    value = min(margin(w,mean(w),1,h) for w in (left,right))
    if value>0:
        return 1,value.__floor__()
    require(right-left>F(1,1000000),'interval cannot be certified with this board')
    c1,m1 = linear(a,b,left,mid)
    c2,m2 = linear(a,b,mid,right)
    return c1+c2,min(m1,m2)


def lattice_checks():
    for n in range(1,8):
        def actual(w,h):
            return sum(max(0,(n*(w-F(j+k,2))).__ceil__())
                       for k in range(h+1) for j in range(max(0,(2*w).__ceil__())))
        for w in (F(9,4),F(17,5),F(11,3)):
            for i in range(3):
                for j in range(3):
                    for k in range(2):
                        weight = F(i,n)+F(j+k,2)
                        lhs = actual(w,3)-actual(w-weight,2)
                        rhs = n*(source(w,3)-source(w-weight,2))
                        require(lhs>=rhs,'ceiling gains under a leading monomial shift')


def verify():
    lattice_checks()
    for h in range(6):
        for w in (F(-1,7),F(1,2),F(7,3),F(29,4)):
            direct = sum((max(F(0),w-F(j+k,2)) for k in range(h+1)
                          for j in range(max(0,(2*w).__ceil__()))),F(0))
            require(source(w,h)==direct,'normalized source')
    primary = source(PRIMARY,2)-rank(11,2)
    require(primary>0 and DEGREE==15,'universal primary')
    require(DEGREE*(2*ORDER*AGREEMENT).__floor__()<LARGE,'mixed Bezout')
    require(AGREEMENT**2<F(1,2) and F(1,2)-AGREEMENT**2>0 and
            AGREEMENT**2>=F(1,2*(ORDER+1))+(AGREEMENT-F(1,2*(ORDER+1)))/LARGE,
            'Johnson separation and zero-derivative factor')
    def ordinary(w,v):
        return 1+(w-F(1,2))/AGREEMENT+(2*w+v)*SIGMA/(2*AGREEMENT)
    def broad(v,left,right):
        return max(min(margin(w,ordinary(w,v),v,h) for w in (left,right))
                   for h in range(v,ORDER,max(1,ORDER//180))).__floor__()
    big = (broad(2,F(1),PRIMARY),broad(1,F(5),PRIMARY))
    require(min(big)>0,'broad variance bounds')
    parts = [linear(a,b,F(b,2),F(b+1,2)) for b in range(1,10) for a in range(b)]
    print(f'Every positive length; agreement {AGREEMENT}; '
          f'characteristic zero or >{ORDER}; list <= {2*LARGE+DEGREE:,}.')
    print(f'Normalized primary surplus {primary}; {sum(c for c,_ in parts)} linear intervals, '
          f'least normalized surplus {min(d for _,d in parts):,}; broad surpluses {big}.')


if __name__=='__main__':
    verify()
