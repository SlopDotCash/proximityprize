#!/usr/bin/env python3
"""Verify the length-independent 249/500 quarter-rate agreement certificate."""

from fractions import Fraction as F

from probe_half_list_uniform_length import source as half_source
from probe_linear_contact_quotient import rank, require, upper_sqrt
from probe_quarter_four_term_units import degeneracy_controls, wronskian_controls


RATE = F(1, 4)
AGREEMENT = F(249, 500)
PRIMARY_ORDER = 8
PRIMARY = PRIMARY_ORDER*AGREEMENT
DEGREE = int(PRIMARY/RATE)
STOCK = 250_000
GROUP = 260_000
SMALL_ORDER = 6_000
LARGE_ORDER = 50_000
CAP = LARGE_ORDER//2
EXCESS = 2*RATE-AGREEMENT
HIGH = 5*RATE+40*EXCESS
INVARIANT_ORDERS = (0, 0, 1, 1, 3, 4, 6)


def source(weight, cap):
    """Quarter-weight columns from the normalized half-weight sum."""
    return half_source(2*weight, cap)/2


def order_floor(weight, degree, order, cap):
    smaller = cap-degree
    source_gain = source(order*AGREEMENT, cap)-source(order*AGREEMENT-weight, smaller)
    return ((source_gain-rank(order, cap)+rank(order, smaller)) /
            (rank(order, smaller)-rank(order-1, smaller)))


def intersection(weight, a, b):
    return a*weight+b*(weight-RATE)-a*b*RATE


def mean_order(weight, a, b, j):
    return (j*(j+1)+1+intersection(weight, a, b))/(2*j)


def intervals(left, right, cuts):
    if left >= right:
        return []
    bounds = sorted({left, right, *(x for x in cuts if left<x<right)})
    return zip(bounds, bounds[1:])


def small_caps():
    return range(300, SMALL_ORDER-299, 300)


def quadratic_factors():
    require(source(PRIMARY, 2)>rank(PRIMARY_ORDER, 2), 'primary interpolation')
    retained = STOCK-DEGREE**2
    require(retained>DEGREE*int(SMALL_ORDER*AGREEMENT/RATE), 'quadratic Bezout')
    sigma = upper_sqrt(RATE-AGREEMENT**2+(AGREEMENT-RATE)/retained)
    order_zero = 3*(1-AGREEMENT**2/(RATE+(2*AGREEMENT-RATE)/retained))
    require(order_zero<=F(1,8), 'order-zero quadratic sites')
    for left,right in intervals(2*RATE, PRIMARY, [i*RATE/16 for i in range(33,260)]):
        def upper(w):
            return 1+(w-RATE)/AGREEMENT+(4*w-F(1,2))*sigma/(2*AGREEMENT)
        require(any(all(order_floor(w,2,SMALL_ORDER,h)>upper(w) for w in (left,right))
                    for h in small_caps()), 'quadratic factor or squarefree product')


def lower_linear_factors():
    nonradial = (DEGREE+2)*(1-AGREEMENT**2/(RATE+(2*AGREEMENT-RATE)/GROUP))
    require(1-nonradial>3*RATE, 'univariate denominator below weight one')
    require(GROUP>DEGREE*int(SMALL_ORDER*AGREEMENT/RATE), 'lower linear Bezout')
    low = AGREEMENT+2*RATE-nonradial
    for b in range(1,5):
        for a in range(b):
            left = max(low, b*RATE, 4*RATE if a==0 else 0)
            for x,y in intervals(left, (b+1)*RATE, [4*RATE+RATE/4,4*RATE+RATE/2]):
                if a in (2,3):
                    require(y-RATE-a*RATE<1-nonradial, 'repeated denominator content')
                def upper(w, j):
                    E = w-RATE
                    if j>0:
                        return mean_order(w,a,b,j)
                    if j<0:
                        return 1+2*E-2*RATE
                    if a==3:
                        return (3+4*E-6*RATE)/2
                    if a==2:
                        return 2+(E-2*RATE)/3+(intersection(w,a,b)-1)/6
                    return 1+2*(E-RATE) if a==1 else 1+E
                comparisons = (-1,0,2,3,4,5) if a==2 else (0,2,3,4,5)
                require(any(all(order_floor(w,1,SMALL_ORDER,h)>upper(w,j) for w in (x,y))
                            for j in comparisons for h in small_caps()), 'lower linear weight')


def upper_linear_factors():
    require(GROUP>int(LARGE_ORDER*AGREEMENT/RATE)+5*CAP and HIGH<6*RATE,
            'exceptional interval and mixed Bezout')
    for b in range(5,DEGREE+1):
        left, right = max(HIGH,b*RATE), min(PRIMARY,(b+1)*RATE)
        for x,y in intervals(left, right, [5*RATE+RATE/16,5*RATE+RATE/4]):
            order = LARGE_ORDER if b==5 else SMALL_ORDER
            caps = (order//5,order//3,order//2,2*order//3,8*order//10)
            require(any(GROUP>int(order*AGREEMENT/RATE)+h*b and
                        all(order_floor(w,1,order,h)>mean_order(w,b-1,b,j) for w in (x,y))
                        for j in (2,3,4,5,6) for h in caps), 'upper linear weight')


def check_point_charges():
    for o,i in enumerate(INVARIANT_ORDERS):
        plane = max(0,o*o-o-1)
        require(i+int(o==3)>=o-1 and i+plane-int(o!=3 and i+plane>0)>=5*o-9,
                'simple branches and finite support')
        require(2*(min(o,3)-int(o==1))>=6*o-7-plane, 'midpoint contact')
        if o<=1:
            lower = -3
        elif o==2:
            lower = 0
        elif o==3:
            require(7*3+21*i+3*plane>=39*o-60, 'ordinary order-three fiber')
            i += 1  # The Hessian content vanishes at the other order-three fibers.
            lower = 0
        else:
            lower = 0
        require(7*lower+21*i+3*plane>=39*o-60, 'involuted-section contact')


def harmonic_factors():
    active = 0
    margins = []
    cuts = [5*RATE+i*EXCESS/8 for i in range(1,321)]
    for left,right in intervals(5*RATE, HIGH, cuts):
        ends = [(w,order_floor(w,1,LARGE_ORDER,CAP)) for w in (left,right)]
        if (all(intersection(w,4,5)+10-5*z<0 for w,z in ends) or
                any(all(z>mean_order(w,4,5,j) for w,z in ends) for j in (2,3,4))):
            continue
        active += 1
        for w,z in ends:
            ell, E = w-5*RATE, w-RATE
            inv, plane = 4*RATE+2*ell, intersection(w,4,5)
            exceptional = plane+10-5*z
            bad = inv+2-z
            require(E<2*(1-exceptional) and E-RATE<1-exceptional,
                    'linear factor with denominator degree at most two')
            require(2*(1-exceptional)>3*E-6*RATE, 'harmonic invariant J')
            require(3*(AGREEMENT-exceptional-ell)>E and
                    6*(AGREEMENT-exceptional)>2*E+RATE+ell and
                    2*(AGREEMENT-bad)>3*RATE+ell, 'repeated and cubic denominators')
            midpoint = 3*z-(7+plane)/2-w-6*(RATE+ell)
            involution = (39*z-60-21*inv-3*plane)/7+3*AGREEMENT-w-12*RATE-6*ell
            support = inv+plane+9-5*z
            branch = 1-bad-8*support
            require(min(midpoint,involution,branch)>0, 'midpoint, involution, and four-term units')
            margins.append((midpoint,involution,branch))
    require(active==105 and len(margins)==2*active, 'terminal interval census')
    certified = (F(66,1000), F(21,1000), F(121,1000))
    require(all(min(row[j] for row in margins)>bound for j,bound in enumerate(certified)),
            'reported normalized margins')
    return active


def verify():
    wronskian_controls()
    degeneracy_controls()
    quadratic_factors()
    lower_linear_factors()
    upper_linear_factors()
    check_point_charges()
    active = harmonic_factors()
    cap = STOCK+GROUP+DEGREE-1
    require(cap==510014 and GROUP>=STOCK, 'large groups and named list cap')
    length = 2**30
    errors = int(length*(1-AGREEMENT))
    require(errors==539018395, 'named length')
    print(f'Agreement {AGREEMENT}, error {1-AGREEMENT}, at most {cap:,} words at every length.')
    print(f'{active} terminal intervals; margins exceed 0.066, 0.021, and 0.121.')
    print(f'At length {length:,}, the closed error ceiling is {errors:,}.')


if __name__=='__main__':
    verify()
