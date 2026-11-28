#!/usr/bin/env python3
"""Check cubic-primary half-rate list bounds at arbitrary positive lengths."""

from fractions import Fraction as F
from functools import lru_cache

from probe_half_joint_occupancy import (
    Board, ORDER, RATE, certify, order_floors, site_order_bound,
    verify_discriminant_charges, vertical_order,
)
from probe_half_list_uniform_length import source
from probe_linear_contact_quotient import N, rank, require


def adaptive(board,v,h,lam,b2,j2):
    """Use fractional hit selections and normalized source differences at every length."""
    r = 2000
    s = board.agreement
    population = board.group-board.degree**2
    variance = RATE-s*s+(s-RATE)/population
    def base(q):
        return rank(q,h)-rank(q,h-v)
    def jump(q):
        return rank(q,h-v)-rank(q-1,h-v)
    slope = F(base(r+8)-base(r-8),16)
    coefficient = jump(r)/s
    least_order = (r-lam*s).__floor__()
    require(least_order>0 and slope>0,'positive local multiplicities and slope')
    for q in range(least_order,(r+lam*(1-s)).__floor__()+1):
        shift = q-r
        delta = F(r*min(abs(shift),abs(shift+1)),lam)**2
        require(base(q)<=base(r)+slope*shift+F(r,2)+b2*delta,'base envelope')
        require(jump(q)<=jump(r)+coefficient*F(shift,lam)+F(r,2)+j2*delta,'jump envelope')
    max_weight = (r-3)*s+lam*variance
    eligible = 2*population*s/(3*s+lam*variance)
    require(eligible>v*int(max_weight/RATE)+h*board.degree,'generic mixed resultant')
    surpluses = []
    steps = 120 if board.refined else 12
    for i in range(steps):
        weight = (r-3)*s+lam*variance*i/steps
        z = variance*(i+1)/steps
        for D in (v*RATE,board.primary):
            cost = (base(r)+F(r,2)+b2*r*r*z+coefficient*(s+D-RATE)
                    +(F(r,2)+j2*r*r*z)*(D/RATE+v))
            surpluses.append(source(weight,h)-source(weight-D,h-v)-cost)
    minimum = min(surpluses)
    require(minimum>0,'normalized adaptive quotient')
    return minimum


@lru_cache(None)
def quartic_sites(board,b,common_root):
    """Stratify a squared linear factor times an irreducible quadratic."""
    s = board.agreement
    sites = []
    for o in range(b+2):
        phi = [vertical_order(o,j,1) for j in range(5)]
        for h in range(phi[-1],max(1,phi[0])+1):
            for radial in (False,True):
                allowed = (4,) if common_root else (2,4)
                if radial and (o<2 or (h==0 and o not in allowed)):
                    continue
                linear_hit = h==0 and (o>=3 or (radial and common_root))
                if board.refined and h>0 and o>=h+3+int(radial):
                    linear_hit = True
                derivative_hit = h==0 and radial
                slope = 0 if radial else F(1,o+1)
                plane = max(0,o*o-o-1) if radial else o*o
                costs = [(0,1,0),(1,-1,0),(s*s,-2*s,1+slope),(plane,0,0)]
                costs.extend((h,max(x-h,0),0) for x in phi)
                costs.extend([(0,max(o-1,0),0),(h,2*linear_hit+int(derivative_hit),0),
                              (h,2*linear_hit,0)])
                # The numerator A cannot vanish identically on a pole factor of B.
                costs.append((F(b*h,2)+o*int(linear_hit),0,0))
                if board.refined:
                    costs.append((F(b*h,2)+o*int(linear_hit),F(b,2)*int(derivative_hit),0))
                if not common_root:
                    costs.append((h+int(linear_hit and derivative_hit),0,0))
                sites.append((o,costs))
    return sites


def quartic_interval(board,b,common_root,left,right,depth=0):
    def bounds(w):
        e = w-RATE
        ordinary = [board.agreement,1-board.agreement,board.variance,4*w+b*e-4*b*RATE]
        return (ordinary+[e-j*RATE for j in range(5)]+[e,e-RATE,e-2*RATE,w+b*(e/2-2*RATE)]
                +([w+b*(e/2-3*RATE/2)] if board.refined else [])
                +([] if common_root else [e-3*RATE]))
    mid = (left+right)/2
    upper = site_order_bound(quartic_sites(board,b,common_root),40,bounds,mid)
    x,y = upper(left),upper(right)
    gap = max(min(lo-x,hi-y) for lo,hi in
              zip(order_floors(board,left,1),order_floors(board,right,1)))
    if gap>0:
        return 1,gap
    require(depth<12,'quartic content and root comparisons')
    a,x = quartic_interval(board,b,common_root,left,mid,depth+1)
    c,y = quartic_interval(board,b,common_root,mid,right,depth+1)
    return a+c,min(x,y)


def verify(board):
    s = board.agreement
    require(source(board.primary,3)>rank(board.primary_order,3),'primary surplus')
    require(board.degree*int(ORDER*s/RATE)<board.group,'linear Bezout')
    require(s*s>RATE/(ORDER+1)+s/board.group,'zero-derivative factor')
    verify_discriminant_charges(board.degree+1)
    for v,b2 in [(2,F(1692,1000)),(3,F(2539,1000))]:
        surplus = adaptive(board,v,300,2600,b2,F(15,1000))
        print(f'Derivative degree {v}, normalized source surplus > {int(surplus):,}.')
    parts = []
    for b in range(1,board.degree+1):
        left,right = b*RATE,min(board.primary,(b+1)*RATE)
        for a in range(b):
            kinds = ('unrestricted',) if a!=4 else ('squarefree','quadratic_square','repeated_linear')
            for kind in kinds:
                if kind=='repeated_linear' and b==5:
                    for common_root in (False,True):
                        parts.append(quartic_interval(board,b,common_root,left,right))
                else:
                    parts.append(certify(board,a,b,1,left,right,kind))
    print(f'{sum(k for k,_ in parts)} linear intervals, least gap {float(min(g for _,g in parts)):.8f}.')
    print(f'List at most {3*board.group+board.degree:,} through {int((1-s)*N):,} named errors.')


if __name__=='__main__':
    verify(Board(F(88,125),13,600_000,quartic=True))
    verify(Board(F(703,1000),14,600_000,quartic=True))
    verify(Board(F(4391,6250),15,600_000,quartic=True,refined=True))
