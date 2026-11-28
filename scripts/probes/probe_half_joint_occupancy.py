#!/usr/bin/env python3
"""Certify the joint-occupancy half-rate bounds, including the quartic denominator."""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cached_property, lru_cache
from itertools import product
from math import prod

from probe_half_list_coefficient_derivatives import content_and_order, dual_proposal, dual_weights
from probe_half_list_uniform_length import source
from probe_linear_contact_quotient import rank, require, upper_sqrt


RATE = F(1, 2)
ORDER = 20_000
CAPS = tuple(ORDER*j//100 for j in range(1,100))


@dataclass(frozen=True)
class Board:
    agreement: F
    primary_order: int
    group: int
    quartic: bool = False

    @cached_property
    def primary(self):
        return self.primary_order*self.agreement

    @cached_property
    def degree(self):
        return int(self.primary/RATE)

    @cached_property
    def variance(self):
        s = self.agreement
        return RATE-s*s+(2*s-RATE)/(self.group-3*self.degree**2)

    @cached_property
    def sigma(self):
        return upper_sqrt(self.variance)


@lru_cache(None)
def order_floors(board,w,v):
    return tuple((source(ORDER*board.agreement,h)-source(ORDER*board.agreement-w,h-v)
                  -rank(ORDER,h)+rank(ORDER,h-v))/(rank(ORDER,h-v)-rank(ORDER-1,h-v))
                 for h in CAPS)


def vertical_order(o,j,v):
    if v==1:
        return max(0,o-j-1,int(o>j))
    return max(0,o-j-2,int(o>j),2*int(o>=j+3))


def discriminant_charge(o):
    return max(6*(o-1)-12,{2:1,3:3,4:7}.get(o,0))


def verify_discriminant_charges(max_order):
    invariant_i = {(0,4):12,(1,3):-3,(2,2):1}
    invariant_j = {(0,2,4):72,(1,2,3):9,(1,1,4):-27,(0,3,3):-27,(2,2,2):-2}
    discriminant = Counter()
    for terms,exponent,scale in ((invariant_i,3,4),(invariant_j,2,-1)):
        for factors in product(terms.items(),repeat=exponent):
            indices = tuple(sorted(j for term,_ in factors for j in term))
            discriminant[indices] += scale*prod(c for _,c in factors)
    monomials = [indices for indices,c in discriminant.items() if c]
    require(len(monomials)==16,'ordinary quartic discriminant terms')
    for o in range(max_order+1):
        local = min(sum(vertical_order(o,j,1) for j in indices) for indices in monomials)
        require(local>=discriminant_charge(o),'quartic discriminant order')


@lru_cache(None)
def costs(board,a,b,v,kind):
    """Coefficients of 1, p, p² for the cost of a site at each integer order."""
    result = []
    for o in range(b+v+1):
        slope_cost = F(1,o+v) if o<=1 else 0
        plane = max(0,o*o-o-1) if v==1 else max(0,o-2)**2+max(0,o-4)
        local = [(0,1,0),(1,-1,0),(board.agreement**2,-2*board.agreement,1+slope_cost),(plane,0,0)]
        content = vertical_order(o,a,v)
        for j in range(a+1):
            excess = vertical_order(o,j,v)-content
            local.append((content,excess,0))
        if kind=="squarefree":
            local.append((discriminant_charge(o),0,0))
        elif kind=="quadratic_square":
            local.append((int(o>=4),0,0))
        elif kind=="repeated_linear":
            local.append((0,1+2*int(o>=3),0))
        local.append((0,max(0,o-1),0))
        result.append(local)
    return result


def limits(board,a,b,w,v,kind):
    e = w-v*RATE
    s = board.agreement
    bounds = [s,1-s,board.variance,a*w+b*e-a*b*RATE]+[e-j*RATE for j in range(a+1)]
    if kind=="squarefree":
        bounds.append(6*e-12*RATE)
    elif kind in ("quadratic_square","repeated_linear"):
        retained = board.group-3*board.degree**2
        nonradial = (b+2)*(1-s*s/(RATE+(2*s-RATE)/retained))
        if kind=="quadratic_square":
            bounds.append(nonradial+e-4*RATE)
        else:
            bounds.append(e-RATE+nonradial+(3*s-1)*(e-4*RATE)+3*board.sigma/2)
    return bounds+[w-RATE]


def joint_bound(board,a,b,mid,v,mesh,kind):
    polynomials = costs(board,a,b,v,kind)
    return site_order_bound(tuple(enumerate(polynomials)),mesh,
                            lambda w: limits(board,a,b,w,v,kind),mid)


def site_order_bound(sites,mesh,bounds,mid):
    """Certify the proposed bound for every real occupancy at every allowed site."""
    orders,polynomials = zip(*sites)
    rows = []
    points = [i/mesh for i in range(mesh+1)]
    for j in range(len(polynomials[0])):
        row = []
        for local in polynomials:
            c,l,q = map(float,local[j])
            row.extend(c+p*(l+p*q) for p in points)
        rows.append(row)
    scores = [o for o in orders for _ in points]
    weights = dual_weights(rows,bounds(mid),scores,max_steps=200)
    require(all(x>=0 for x in weights),'dual signs')
    bias = F(0)
    for o,local in sites:
        c,l,q = [-sum(x*y[j] for x,y in zip(weights,local)) for j in range(3)]
        c += o
        bias = max(bias,c,c+l+q)
        if q<0 and 0 < -l/(2*q) < 1:
            bias = max(bias,c-l*l/(4*q))
    return lambda w: bias+sum(x*y for x,y in zip(weights,bounds(w)))


def preliminary_bound(board,a,b,mid,v):
    if v==2:
        return lambda w: 1+(w-RATE)/board.agreement+(2*w+2)*board.sigma/(2*board.agreement)
    orders = range(1,b+2)
    rows = [[max(0,o*o-o-1) for o in orders]]
    for j in range(a+1):
        row = []
        for o in orders:
            h,q = content_and_order(o,a,j)
            row.append(h+(1 if j==a else board.agreement)*q)
        rows.append(row)
    rows.append(list(orders))
    def rhs(w):
        e = w-RATE
        bounds = [a*w+b*e-a*b*RATE]
        for j in range(a+1):
            height = max(content_and_order(o,a,j)[1] for o in range(b+2))
            bounds.append(e-j*RATE+(board.sigma*height/2 if j<a else 0))
        bounds.append((board.agreement+e+(1-board.agreement)*a/2+board.sigma*(b+1))
                      /(board.agreement+(1-board.agreement)/2))
        return bounds
    weights,bias = dual_proposal(rows,rhs(mid))
    return lambda w: bias+sum(x*y for x,y in zip(weights,rhs(w)))


def certify(board,a,b,v,left,right,kind,depth=0):
    mid = (left+right)/2
    def gap(mean):
        low,high = mean(left),mean(right)
        return max(min(x-low,y-high) for x,y in zip(order_floors(board,left,v),order_floors(board,right,v)))
    margin = gap(preliminary_bound(board,a,b,mid,v))
    if margin>0:
        return 1,margin
    for mesh in ((40,100) if depth<=2 else (120,)):
        margin = gap(joint_bound(board,a,b,mid,v,mesh,kind))
        if margin>0:
            return 1,margin
    require(depth<12,f'inconclusive half-rate interval at {v=}, {a=}, {b=}, {mid=}')
    n1,m1 = certify(board,a,b,v,left,mid,kind,depth+1)
    n2,m2 = certify(board,a,b,v,mid,right,kind,depth+1)
    return n1+n2,min(m1,m2)


def verify(board,expected_errors):
    s = board.agreement
    if board.quartic:
        verify_discriminant_charges(board.degree+1)
    require(source(board.primary,2)>rank(board.primary_order,2),'primary surplus')
    require(board.degree*int(ORDER*s/RATE)<board.group,'generic Bezout')
    require(s*s>RATE/(ORDER+1)+s/board.group,'zero-derivative factor')
    for v in (1,2):
        parts = []
        for b in range(v,board.degree+1):
            for a in range(b-v+1):
                kinds = ("unrestricted",)
                if board.quartic and v==1 and a==4:
                    kinds = ("squarefree","quadratic_square","repeated_linear")
                for kind in kinds:
                    parts.append(certify(board,a,b,v,b*RATE,min(board.primary,(b+1)*RATE),kind))
        margin = min(x for _,x in parts)
        require(margin>0,'strict interval comparison')
        print(f'Derivative degree {v}: {sum(n for n,_ in parts)} intervals; '
              f'minimum certified mean-order gap {float(margin):.8f}.')
    errors = int((1-s)*2**30)
    require(errors==expected_errors,'named error radius')
    print(f'Agreement {s}, list at most {2*board.group+board.degree:,}, named safe errors {errors:,}.')


if __name__=='__main__':
    verify(Board(F(353,500),12,500_000),315_680_096)
    verify(Board(F(1411,2000),13,600_000,quartic=True),316_216_967)
