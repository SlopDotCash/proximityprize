#!/usr/bin/env python3
"""Verify length-independent list bounds at rates one eighth and one sixteenth."""
from fractions import Fraction as F

from probe_half_list_coefficient_derivatives import content_and_order, dual_proposal
from probe_half_list_uniform_length import source as half_source
from probe_linear_contact_quotient import rank, require
from probe_sixteenth_list_quotient_jets import upper_sqrt


def certify(q,s,primary_order,large,cutoff):
    r = 425
    rate = F(1,q)
    primary = primary_order*s
    degree = (q*primary).__floor__()
    sigma = upper_sqrt(rate-s*s+(s-rate)/(large-degree**2))
    def source(w,h):
        return F(2,q)*half_source(q*w/2,h)
    def margin(w,mean,v,h):
        return (source(r*s,h)-source(r*s-w,h-v)-rank(r,h)+rank(r,h-v)
                -(rank(r,h-v)-rank(r-1,h-v))*mean)
    def data(a,b,w):
        orders = list(range(1,b+2))
        e = w-rate
        rows = [tuple(max(0,o*o-o-1) for o in orders)]
        bounds = [a*w+b*e-a*b*rate]
        for j in range(a+1):
            local = [content_and_order(o,a,j) for o in orders]
            factor = 1 if j==a else s
            rows.append(tuple(h+factor*u for h,u in local))
            bound = e-j*rate
            if j<a:
                bound+=sigma*max(u for _,u in local)/2
            bounds.append(bound)
        rows.append(tuple(orders))
        bounds.append((s+e+(1-s)*a/2+sigma*(b+1))/(s+(1-s)/2))
        return rows,bounds
    def certify_linear(a,b,left,right):
        mid = (left+right)/2
        rows,bounds = data(a,b,mid)
        coeff,bias = dual_proposal(rows,bounds)
        def mean(w):
            return bias+sum(c*u for c,u in zip(coeff,data(a,b,w)[1]))
        h = max(range(1,r,2),key=lambda k:margin(mid,mean(mid),1,k))
        surplus = min(margin(w,mean(w),1,h) for w in (left,right))
        if surplus>0:
            return 1,surplus.__floor__()
        require(right-left>F(1,1_000_000),'linear intervals retain positive margins')
        c1,v1 = certify_linear(a,b,left,mid)
        c2,v2 = certify_linear(a,b,mid,right)
        return c1+c2,min(v1,v2)
    def broad(v,left):
        def ordinary(w):
            return 1+(w-rate)/s+(q*w+v)*sigma/(2*s)
        value = max(min(margin(w,ordinary(w),v,h) for w in (left,primary))
                    for h in range(v,r,2))
        require(value>0,'quadratic and high linear weights')
        return value.__floor__()
    for h in range(6):
        for w in (F(1,q),F(7,5),F(9,4)):
            direct = sum(max(0,w-F(j+k,q)) for k in range(h+1)
                         for j in range((q*w).__ceil__()))
            require(source(w,h)==direct,'normalized source transformation')
    primary_margin = source(primary,2)-rank(primary_order,2)
    require(primary_margin>0 and degree*(q*r*s).__floor__()<large,'primary and Bezout')
    require(s*s<rate and s*s>rate/(r+1)+(s-rate/(r+1))/large,'Johnson and Frobenius')
    broad_margins = broad(2,2*rate),broad(1,cutoff*rate)
    low = [certify_linear(a,b,b*rate,(b+1)*rate) for b in range(1,cutoff)
           for a in range(b)]
    print(f'1/{q}, agreement {s}, list <= {2*large+degree:,} at every length. '
          f'Primary surplus {primary_margin}, broad surpluses {broad_margins}, '
          f'{sum(c for c,_ in low)} linear intervals, minimum surplus {min(v for _,v in low)}.')


if __name__=='__main__':
    certify(8,F(3533,10000),6,24_992,8)
    certify(16,F(2499,10000),5,39_990,15)
