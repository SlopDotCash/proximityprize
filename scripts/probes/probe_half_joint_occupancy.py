#!/usr/bin/env python3
"""Certify the half-rate list bound at agreement 353/500 on every injective grid."""

from fractions import Fraction as F
from functools import lru_cache

from probe_half_list_coefficient_derivatives import content_and_order, dual_proposal, dual_weights
from probe_half_list_uniform_length import source
from probe_linear_contact_quotient import rank, require, upper_sqrt


RATE = F(1, 2)
AGREEMENT = F(353, 500)
ORDER = 20_000
GROUP = 500_000
PRIMARY = 12*AGREEMENT
DEGREE = int(PRIMARY/RATE)
VARIANCE = RATE-AGREEMENT**2+(2*AGREEMENT-RATE)/(GROUP-3*DEGREE**2)
SIGMA = upper_sqrt(VARIANCE)
CAPS = tuple(ORDER*j//100 for j in range(1,100))


@lru_cache(None)
def order_floors(w,v):
    return tuple((source(ORDER*AGREEMENT,h)-source(ORDER*AGREEMENT-w,h-v)
                  -rank(ORDER,h)+rank(ORDER,h-v))/(rank(ORDER,h-v)-rank(ORDER-1,h-v))
                 for h in CAPS)


def vertical_order(o,j,v):
    if v==1:
        return max(0,o-j-1,int(o>j))
    return max(0,o-j-2,int(o>j),2*int(o>=j+3))


@lru_cache(None)
def costs(a,b,v):
    """Coefficients of 1, p, p² for the cost of a site at each integer order."""
    result = []
    for o in range(b+v+1):
        slope_cost = F(1,o+v) if o<=1 else 0
        plane = max(0,o*o-o-1) if v==1 else max(0,o-2)**2+max(0,o-4)
        local = [(0,1,0),(1,-1,0),(AGREEMENT**2,-2*AGREEMENT,1+slope_cost),(plane,0,0)]
        content = vertical_order(o,a,v)
        for j in range(a+1):
            excess = vertical_order(o,j,v)-content
            local.append((content,excess,0))
        local.append((0,max(0,o-1),0))
        result.append(local)
    return result


def limits(a,b,w,v):
    e = w-v*RATE
    return ([AGREEMENT,1-AGREEMENT,VARIANCE,a*w+b*e-a*b*RATE]
            +[e-j*RATE for j in range(a+1)]+[w-RATE])


def joint_bound(a,b,mid,v,mesh):
    polynomials = costs(a,b,v)
    rows = []
    points = [i/mesh for i in range(mesh+1)]
    for j in range(len(polynomials[0])):
        row = []
        for local in polynomials:
            c,l,q = map(float,local[j])
            row.extend(c+p*(l+p*q) for p in points)
        rows.append(row)
    scores = [o for o in range(len(polynomials)) for _ in points]
    weights = dual_weights(rows,limits(a,b,mid,v),scores,max_steps=200)
    require(all(x>=0 for x in weights),'dual signs')
    bias = F(0)
    for o,local in enumerate(polynomials):
        c,l,q = [-sum(x*y[j] for x,y in zip(weights,local)) for j in range(3)]
        c += o
        bias = max(bias,c,c+l+q)
        if q<0 and 0 < -l/(2*q) < 1:
            bias = max(bias,c-l*l/(4*q))
    return lambda w: bias+sum(x*y for x,y in zip(weights,limits(a,b,w,v)))


def preliminary_bound(a,b,mid,v):
    if v==2:
        return lambda w: 1+(w-RATE)/AGREEMENT+(2*w+2)*SIGMA/(2*AGREEMENT)
    orders = range(1,b+2)
    rows = [[max(0,o*o-o-1) for o in orders]]
    for j in range(a+1):
        row = []
        for o in orders:
            h,q = content_and_order(o,a,j)
            row.append(h+(1 if j==a else AGREEMENT)*q)
        rows.append(row)
    rows.append(list(orders))
    def rhs(w):
        e = w-RATE
        bounds = [a*w+b*e-a*b*RATE]
        for j in range(a+1):
            height = max(content_and_order(o,a,j)[1] for o in range(b+2))
            bounds.append(e-j*RATE+(SIGMA*height/2 if j<a else 0))
        bounds.append((AGREEMENT+e+(1-AGREEMENT)*a/2+SIGMA*(b+1))
                      /(AGREEMENT+(1-AGREEMENT)/2))
        return bounds
    weights,bias = dual_proposal(rows,rhs(mid))
    return lambda w: bias+sum(x*y for x,y in zip(weights,rhs(w)))


def certify(a,b,v,left,right,depth=0):
    mid = (left+right)/2
    def gap(mean):
        low,high = mean(left),mean(right)
        return max(min(x-low,y-high) for x,y in zip(order_floors(left,v),order_floors(right,v)))
    margin = gap(preliminary_bound(a,b,mid,v))
    if margin>0:
        return 1,margin
    for mesh in ((40,100) if depth<=2 else (120,)):
        margin = gap(joint_bound(a,b,mid,v,mesh))
        if margin>0:
            return 1,margin
    require(depth<12,f'inconclusive half-rate interval at {v=}, {a=}, {b=}, {mid=}')
    n1,m1 = certify(a,b,v,left,mid,depth+1)
    n2,m2 = certify(a,b,v,mid,right,depth+1)
    return n1+n2,min(m1,m2)


def verify():
    require(source(PRIMARY,2)>rank(12,2) and DEGREE==16,'primary surplus')
    require(DEGREE*int(ORDER*AGREEMENT/RATE)<GROUP,'generic Bezout')
    require(AGREEMENT**2>RATE/(ORDER+1)+AGREEMENT/GROUP,'zero-derivative factor')
    for v in (1,2):
        parts = [certify(a,b,v,b*RATE,min(PRIMARY,(b+1)*RATE))
                 for b in range(v,DEGREE+1) for a in range(b-v+1)]
        margin = min(x for _,x in parts)
        require(margin>F(1,1_000_000),'reported strict interval margin')
        print(f'Derivative degree {v}: {sum(n for n,_ in parts)} intervals; '
              f'minimum certified mean-order gap {float(margin):.8f}.')
    limit = 2*GROUP+DEGREE
    errors = int((1-AGREEMENT)*2**30)
    require(errors==315680096 and limit==1000016,'named outputs')
    print(f'Agreement {AGREEMENT}, list at most {limit:,}, named safe errors {errors:,}.')


if __name__=='__main__':
    verify()
