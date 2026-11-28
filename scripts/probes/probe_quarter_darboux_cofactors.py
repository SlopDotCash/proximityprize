#!/usr/bin/env python3
"""Named quarter-rate interpolation, cofactor rank, and split-fiber bounds."""

from fractions import Fraction as F

from probe_linear_contact_quotient import rank, require, upper_sqrt
from probe_quarter_uniform_four_term import source, intervals, intersection, mean_order


N = 2**30
R = F(1, 4)
S = F(4977, 10000)
STOCK = 250_000
GROUP = N - 250_100
PRIMARY = 8*S
DEGREE = int(PRIMARY/R)
SMALL = 6_000
LARGE = 50_000
HIGH = 5*R + 40*(2*R-S)
CAPS = tuple(range(300, SMALL, 300))


def floor_order(weight, v, order, cap):
    remaining = cap-v
    gain = source(order*S, cap)-source(order*S-weight, remaining)
    return ((gain-rank(order, cap)+rank(order, remaining)) /
            (rank(order, remaining)-rank(order-1, remaining)))


def quadratic_control(left, right, a, alpha, sigma):
    """Certify an affine majorant of the order mean or its centered second moment."""
    orders = range(int(left/R)+3)
    cost = [next(i for i in range(o+1) if o<=a+i+min(i,2)) for o in orders]
    middle = (left+right)/2
    for center in [None]+[F(i,2) for i in range(2*orders[-1]+1)]:
        values = [o if center is None else (o-center)**2 for o in orders]
        slopes = {F(0)}
        for i in orders:
            for j in range(i):
                if cost[i]!=cost[j]:
                    slope = F(values[i]-values[j],cost[i]-cost[j])
                    if slope>=0:
                        slopes.add(slope)

        def line(slope):
            regular = max(values[i]-slope*cost[i] for i in orders if i>=2)
            extra = max(0,max(values[i]-slope*cost[i]-regular for i in (0,1)))
            return regular+extra*alpha

        slope = min(slopes, key=lambda u:line(u)+u*(middle-(2+a)*R))
        constant = line(slope)
        def bound(w):
            return constant+slope*(w-(2+a)*R)

        if center is None:
            def upper(w):
                return bound(w)
        else:
            root = upper_sqrt(max(F(0),bound(middle)))
            if not root:
                continue
            def upper(w):
                return 1+(w-R)/S+sigma*(bound(w)+root**2)/(2*root*S)
        if any(all(floor_order(w,2,SMALL,h)>upper(w) for w in (left,right)) for h in CAPS):
            return True
    return False


def quadratic_factors():
    retained = STOCK-DEGREE**2
    require(source(PRIMARY,2)>rank(8,2), 'primary interpolation')
    require(retained>DEGREE*int(SMALL*S/R), 'quadratic Bezout')
    sigma = upper_sqrt(R-S**2+(S-R)/retained)
    alpha = 4*(1-S**2/(R+(2*S-R)/retained))
    require(alpha<=F(1,16), 'order-zero and order-one slope bound')
    extra = 0
    for left,right in intervals(2*R,PRIMARY,[i*R/16 for i in range(33,260)]):
        def upper(w):
            return 1+(w-R)/S+(4*w-1)*sigma/(2*S)
        if any(all(floor_order(w,2,SMALL,h)>upper(w) for w in (left,right)) for h in CAPS):
            continue
        for a in range(int(left/R)-1):
            require(quadratic_control(left,right,a,alpha,sigma),'leading-coefficient contact')
        extra += 1
    require(extra==22,'quadratic interval census')


def exterior_factors():
    nonradial = (DEGREE+2)*(1-S**2/(R+(2*S-R)/GROUP))
    require(1-nonradial>3*R and GROUP>DEGREE*int(SMALL*S/R),'lower-weight prerequisites')
    for b in range(1,5):
        for a in range(b):
            left = max(S+2*R-nonradial,b*R,4*R if a==0 else 0)
            for x,y in intervals(left,(b+1)*R,[4*R+R/4,4*R+R/2]):
                if a in (2,3):
                    require(y-R-a*R<1-nonradial,'repeated denominator content')
                def upper(w,j):
                    E = w-R
                    if j>0:
                        return mean_order(w,a,b,j)
                    if j<0:
                        return 1+2*E-2*R
                    if a==3:
                        return (3+4*E-6*R)/2
                    if a==2:
                        return 2+(E-2*R)/3+(intersection(w,a,b)-1)/6
                    return 1+2*(E-R) if a==1 else 1+E
                tests = (-1,0,2,3,4,5) if a==2 else (0,2,3,4,5)
                require(any(all(floor_order(w,1,SMALL,h)>upper(w,j) for w in (x,y))
                            for j in tests for h in CAPS),'lower linear weights')
    for b in range(5,DEGREE+1):
        for x,y in intervals(max(HIGH,b*R),min(PRIMARY,(b+1)*R),[5*R+R/16,5*R+R/4]):
            order = LARGE if b==5 else SMALL
            for h in (order//5,order//3,order//2,2*order//3,8*order//10):
                if GROUP>int(order*S/R)+h*b and any(
                    all(floor_order(w,1,order,h)>mean_order(w,b-1,b,j) for w in (x,y))
                    for j in (2,3,4,5,6)):
                    break
            else:
                raise AssertionError('upper linear weights')


def cofactor_bound():
    # The two tangents of the lower convex envelope of (o^2-o-1)_+ at o=3.
    tangents = ((4,7),(6,13))
    for o in range(7):
        for slope,intercept in tangents:
            require(max(0,o*o-o-1)>=slope*o-intercept,'intersection tangent')
            if o<=1:
                require(1-(slope*o-intercept)>=o+1,'small-order slope classes')
            elif o>=2:
                require(o*o-(o*o-o-1)==o+1,'missing radial initial form')
    J = F(1,10)
    for x,y in intervals(5*R,HIGH,[5*R+i*(2*R-S)/8 for i in range(1,321)]):
        require(any(GROUP>int(LARGE*S/R)+5*h and
                    all(intersection(w,4,5)+offset-lam*floor_order(w,1,LARGE,h)<=J
                        for w in (x,y))
                    for lam,offset in tangents
                    for h in (24_000,25_000,25_500,26_000,27_000,28_000,29_000,30_000)),
                'excess collision classes')
    eta = R-S**2+(1+J)/GROUP
    mu = upper_sqrt(R+F(1,GROUP))
    union = 1-(1-mu)**4+F(6,GROUP)
    rank_cap = int(N*(union+4*upper_sqrt(J*eta)))+5
    nullity = GROUP-rank_cap
    require(nullity>800_000,'independent logarithmic forms')
    degree = (GROUP-1)//(nullity-1)
    branches = 2*degree-2
    moving = 5
    split_cap = 4+branches+3+6*(branches+2)*moving
    require(nullity+1>split_cap,'tame split-fiber bound')
    require(N*S>F(N,GROUP)+F(GROUP-1,GROUP-2)*R*N,'Riccati agreement count')
    require(GROUP+STOCK+DEGREE<=N+1,'stock deduction')
    require(6*(N//4)*GROUP**2<2**157,'separability on either named prime')
    errors = int(N*(1-S))
    require(errors==539_340_518,'integer conversion')
    return errors,rank_cap,nullity,degree,split_cap


if __name__=='__main__':
    quadratic_factors()
    exterior_factors()
    e,dim,k,m,split = cofactor_bound()
    print(f'Quarter rate at {S} agreement on {N:,} sites: safe through {e:,} errors.')
    print(f'Cofactor rank at most {dim:,}; nullity at least {k:,}.')
    print(f'First-integral degree at most {m}; at most {split:,} split fibers with a moving branch.')
