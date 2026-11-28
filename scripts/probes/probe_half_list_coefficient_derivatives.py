#!/usr/bin/env python3
"""Certify half-rate decoding via derivatives of a linear equation's denominator."""
from fractions import Fraction as F
from math import isqrt

from probe_linear_contact_quotient import N, rank, require, slots
from probe_sixteenth_list_quotient_jets import upper_sqrt

D = N//2-1
EXTRA = 500_000
T = isqrt(N*D)-EXTRA
S = F(T,N)
R = 2500
PRIMARY = 11*T
DEGREE = (PRIMARY-1)//(D-1)
LARGE = 54_000
SIGMA = upper_sqrt(F(D,N)-S*S+(S-F(D,N))/(LARGE-DEGREE**2))


def fast_slots(weight, cap):
    """Sum the two ranges where ceil((weight+k)/d) is fixed."""
    last = min(cap,(weight-1)//(D-1))
    if last<0:
        return 0
    require(last<D, 'at most one breakpoint for the ceiling')
    height = (weight+D-1)//D
    split = min(last,height*D-weight)
    def segment(lo,hi,m):
        length = hi-lo+1
        linear = (lo+hi)*length//2
        quadratic = hi*(hi+1)*(2*hi+1)//6-(lo-1)*lo*(2*lo-1)//6
        return (length*m*(2*weight-D*(m-1))+(2*m-2*weight-D)*linear
                +(D-2)*quadratic)//2
    return segment(0,split,height)+segment(split+1,last,height+1)


def content_and_order(o, a, j):
    if o<=a:
        return 0,max(o-j-1,int(o>=j+1))
    content = max(1,o-a-1)
    return content,max(o-j-1-content,0)


def contact_values(a, maximum):
    orders = list(range(1,maximum+1))
    rows = [tuple(max(0,o*o-o-1) for o in orders)]
    for j in range(a+1):
        values = [content_and_order(o,a,j) for o in orders]
        factor = 1 if j==a else S
        rows.append(tuple(h+factor*q for h,q in values))
    rows.append(tuple(orders))
    return rows


def limits(weight,a,b,maximum):
    e = weight-D+1
    values = [F(a*weight+b*e-a*b*D,N)]
    for j in range(a+1):
        bound = F(e-j*D,N)
        if j<a:
            height = max(content_and_order(o,a,j)[1] for o in range(maximum+1))
            bound += SIGMA*height/2
        values.append(bound)
    values.append((S+F(e,N)+(1-S)*a/2+SIGMA*maximum)/(S+(1-S)/2))
    return values


def dual_weights(rows, bounds, scores, max_steps=100):
    # Floating point only proposes nonnegative rational multipliers. The exact
    # pointwise inequality and both interval surpluses are rechecked below.
    matrix = [[1]*len(rows[0])]+list(rows)
    rhs = [1]+list(map(float,bounds))
    size = len(matrix)
    source = len(rows[0])
    tab = [[float(x) for x in row]+[float(i==j) for j in range(size)]+[rhs[i]]
           for i,row in enumerate(matrix)]
    objective = [-float(o) for o in scores]+[0.]*(size+1)
    for _ in range(max_steps):
        k = min(range(len(objective)-1),key=objective.__getitem__)
        if objective[k]>=-1e-8:
            break
        pivot = min((row[-1]/row[k],i) for i,row in enumerate(tab) if row[k]>1e-8)[1]
        new = [x/tab[pivot][k] for x in tab[pivot]]
        for i,row in enumerate(tab):
            if i!=pivot:
                tab[i] = [x-row[k]*y for x,y in zip(row,new)]
        objective = [x-objective[k]*y for x,y in zip(objective,new)]
        tab[pivot] = new
    return [F(max(0.,x)).limit_denominator(10000) for x in objective[source+1:-1]]


def dual_proposal(rows, bounds):
    source = len(rows[0])
    coeff = dual_weights(rows, bounds, range(1,source+1))
    # Include order zero, which can have all its probability in a slack variable.
    intercept = max([F(0)]+[i+1-sum(c*row[i] for c,row in zip(coeff,rows))
                              for i in range(source)])
    return coeff,intercept


def margin(weight, mean, v, cap):
    return (fast_slots(R*T,cap)-fast_slots(R*T-weight,cap-v)
            -N*(rank(R,cap)-rank(R,cap-v)+(rank(R,cap-v)-rank(R-1,cap-v))*mean))


def linear_interval(a,b,left,right):
    maximum = b+1
    rows = contact_values(a,maximum)
    mid = (left+right)//2
    coeff,intercept = dual_proposal(rows,limits(mid,a,b,maximum))
    def upper(w):
        return intercept+sum(c*v for c,v in zip(coeff,limits(w,a,b,maximum)))
    mid_mean = upper(mid)
    options = range(1,R,max(1,R//100))
    cap = max(options,key=lambda h: margin(mid,mid_mean,1,h))
    worst = min(margin(w,upper(w),1,cap) for w in (left,right))
    if worst>0:
        return 1,worst.__floor__()
    require(left<right, f'linear weight {left} at denominator degree {a} has surplus {worst}')
    split = (left+right)//2
    n1,m1 = linear_interval(a,b,left,split)
    n2,m2 = linear_interval(a,b,split+1,right)
    return n1+n2,min(m1,m2)


def verify():
    for w in (D-1,4*D+184,5*D-9,PRIMARY, R*T-1):
        for cap in (0,1,27,237,R//2):
            require(fast_slots(w,cap)==slots(w,cap,D),'independent source sum')
    primary_surplus = fast_slots(PRIMARY,2)-N*rank(11,2)
    require(primary_surplus>0 and DEGREE**2<LARGE,'quadratic primary')
    require(DEGREE*((R*T-1)//(D-1))<LARGE and 2*LARGE+DEGREE<=N,
            'generic Bezout and size of the list')
    def variance_mean(w,v):
        return 1+F(w-D+1,T)+(F(w,D)+v)*SIGMA/(2*S)
    # This bound is affine in w, so one cap proving both endpoints suffices.
    def variance_interval(v,left,right):
        return max(min(margin(w,variance_mean(w,v),v,h) for w in (left,right))
                   for h in range(v,R,20)).__floor__()
    broad = (variance_interval(2,2*(D-1),PRIMARY-1),
             variance_interval(1,10*D,PRIMARY-1))
    require(min(broad)>0,'high-weight linear and unrestricted quadratic factors')
    cuts = sorted({D-1,10*D}|{j*D-i for j in range(1,11) for i in (0,1)
                              if D-1<=j*D-i<=10*D})
    count,worst = 0,None
    for left,stop in zip(cuts,cuts[1:]):
        b = left//D
        for a in range((left-D+1)//D+1):
            cases,margin_bound = linear_interval(a,b,left,stop-1)
            count+=cases
            worst = margin_bound if worst is None else min(worst,margin_bound)
    print(f'{N-T:,} safe errors, upper list size {2*LARGE+DEGREE:,}.')
    print(f'Primary surplus {primary_surplus:,}; {count} linear intervals, '
          f'minimum surplus {worst:,}; broad secondary surpluses {broad}.')


if __name__=='__main__':
    verify()
