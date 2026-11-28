#!/usr/bin/env python3
"""Check the length-independent quarter-rate list bound and its harmonic terminal case."""
from fractions import Fraction as F

from probe_half_list_coefficient_derivatives import content_and_order, dual_proposal
from probe_half_list_uniform_length import source as half_source
from probe_linear_contact_quotient import rank, require
from probe_sixteenth_list_quotient_jets import upper_sqrt


RATE = F(1, 4)
AGREEMENT = F(499_999, 1_000_000)
PRIMARY = 8*AGREEMENT
DEGREE = int(4*PRIMARY)
ORDER = 1_000_000
GROUP = 30_000_000
EXCESS = F(1, 1000)
SIGMA = upper_sqrt(RATE-AGREEMENT**2+(AGREEMENT-RATE)/(GROUP-DEGREE**2), 10**15)


def source(weight, cap):
    return half_source(2*weight, cap)/2


def order_floor(weight, degree, cap):
    smaller = cap-degree
    return ((source(ORDER*AGREEMENT, cap)-source(ORDER*AGREEMENT-weight, smaller)
             -rank(ORDER, cap)+rank(ORDER, smaller))
            / (rank(ORDER, smaller)-rank(ORDER-1, smaller)))


def local_rows(a, b, weight):
    orders = tuple(range(1, b+2))
    e = weight-RATE
    rows = [tuple(max(0, o*o-o-1) for o in orders)]
    bounds = [a*weight+b*e-a*b*RATE]
    for j in range(a+1):
        local = [content_and_order(o, a, j) for o in orders]
        fraction = 1 if j==a else AGREEMENT
        rows.append(tuple(c+fraction*t for c, t in local))
        bound = e-j*RATE
        if j<a:
            bound += SIGMA*max(t for _, t in local)/2
        bounds.append(bound)
    rows.append(orders)
    bounds.append((AGREEMENT+e+(1-AGREEMENT)*a/2+SIGMA*(b+1))/(AGREEMENT+(1-AGREEMENT)/2))
    return rows, bounds


def linear_margin(a, b):
    left = b*RATE+(EXCESS if (a,b)==(4,5) else 0)
    right = (b+1)*RATE
    bounds = []
    for j in range(2, 8):
        def intersection(weight, j=j):
            return (j*(j+1)+1+a*weight+b*(weight-RATE)-a*b*RATE)/(2*j)
        bounds.append(intersection)
    if a==3 and b<=5:
        bounds.append(lambda w: (3+4*(w-RATE)-6*RATE)/2)
    if b<=5:
        rows, limits = local_rows(a,b,(left+right)/2)
        coeff, bias = dual_proposal(rows, limits)
        bounds.append(lambda w: bias+sum(c*v for c,v in zip(coeff,local_rows(a,b,w)[1])))
    caps = [ORDER*j//50 for j in (1,3,8,16,20,25,27,30,32,35,40)]
    return max(min(order_floor(w,1,h)-bound(w) for w in (left,right))
               for h in caps for bound in bounds)


def quotient_controls():
    prime = 101
    for a,b in ((2,9),(3,7),(8,4)):
        q = a*b*pow(4,-1,prime) % prime
        w = a*pow(b,-1,prime) % prime
        for y in range(prime):
            numerator = y*y-a*y+q
            denominator = y*y-b*y+q
            require((numerator**2-w*denominator**2-(1-w)*(y*y-q)**2)%prime==0,
                    'branch values in the orbit coordinate')
    values = (2,7,9,15)
    for constant,linear,quadratic in ((3,5,4),(7,0,2),(2,11,0)):
        def derivative(x):
            return (constant+linear*x+quadratic*x*x)%prime
        def log_difference(i,j):
            x,y = values[i],values[j]
            return (derivative(x)-derivative(y))*pow(x-y,-1,prime) % prime
        require((log_difference(0,1)+log_difference(2,3)
                 -log_difference(0,3)-log_difference(2,1))%prime==0,
                'Riccati cross ratio derivative')


def verify():
    quotient_controls()
    require(source(PRIMARY,2)>rank(8,2) and DEGREE==15, 'primary source surplus')
    require(DEGREE*int(4*ORDER*AGREEMENT)<GROUP, 'secondary Bezout')
    require(AGREEMENT**2<RATE and AGREEMENT**2>(1-1/GROUP)*RATE/(ORDER+1)+AGREEMENT/GROUP,
            'outside Johnson and zero-derivative factor')
    nonradial = (DEGREE+2)*(1-AGREEMENT**2/(RATE+(2*AGREEMENT-RATE)/GROUP))
    require(1-nonradial>F(1,2), 'repeated cubic denominator content')
    quadratic = max(min(order_floor(w,2,h)-1-(w-RATE)/AGREEMENT-(4*w+2)*SIGMA/(2*AGREEMENT)
                        for w in (2*RATE,PRIMARY)) for h in (ORDER*i//25 for i in range(1,25)))
    parts = [linear_margin(a,b) for b in range(1,DEGREE+1) for a in range(b)]
    require(quadratic>F(45,100) and min(parts)>F(8,10000), 'noncritical weights')
    exceptions = []
    for w in (5*RATE,5*RATE+EXCESS):
        ell = w-5*RATE
        e = w-RATE
        z = order_floor(w,1,ORDER//3)
        resultant = 4*w+5*e-20*RATE
        t = resultant+10-5*z
        bad = 2*t+2*ell
        require(2*(1-t)>3*e-6*RATE, 'harmonic cubic invariant')
        require(3*(AGREEMENT-t-ell)>e, 'repeated quartic')
        require(3*(1-bad-(2*RATE+ell))>w+6*(ell+2*RATE-AGREEMENT+bad),
                'involuted sections solve the equation')
        exceptions.append(7*t+12*ell)
    require(max(exceptions)<F(6,10000),'common exceptional set')
    # All bounds here are normalized by n, using n >= 1000.
    exc = F(1,1000)+F(6,10000)
    h = exc
    coefficient = 75*h+5*exc+F(10,1000)
    require(max(2*coefficient,20*h)<(1-exc)/2,'branch height and Riccati alternatives')
    require(AGREEMENT*1000>F(1000,2)-F(1,2),'rounding for short lengths')
    print(f'Agreement {AGREEMENT}, maximum list {2*GROUP+DEGREE:,}, every positive length.')
    print(f'{len(parts)} linear intervals, order gaps > 0.0008; quadratic order gap > 0.45.')
    print('Normalized finite exceptional support < 0.0006; full exception count < 1 + 0.0006n.')


if __name__=='__main__':
    verify()
