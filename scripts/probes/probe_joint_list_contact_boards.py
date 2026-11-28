#!/usr/bin/env python3
"""Exact cubic-primary certificates combining adaptive and exterior contact bounds."""
from fractions import Fraction as F
from math import isqrt

from probe_linear_contact_quotient import N, rank, require, slots


# Rate denominator, budget multiplier, excess below floor(sqrt(nd)), primary order,
# then the secondary (derivative degree, cap, occupancy slope, curvature bounds, cutoff).
BOARDS = [
    (16,1,11_500_000,9,[(2,600,7109,'12.8','.55',4),(3,700,6902,'18','.7',4)]),
    (8,1,3_500_000,6,[(2,500,4999,'6.4','.25',3),(3,600,4857,'9','.35',3)]),
    (8,2,11_500_000,9,[(2,500,5107,'6.65','.25',4),(3,600,4963,'9.4','.35',4)]),
    (4,2,7_000_000,9,[(2,400,3650,'3.45','.15',3),(3,500,3549,'4.85','.2',3)]),
]


def adaptive(v,h,lam,b2,j2,cutoff,d,t,primary,base_degree,stock):
    return adaptive_interval(v,h,lam,b2,j2,d,t,base_degree,stock,2000,12,
                             (cutoff*(d-1),primary-1))


def adaptive_interval(v,h,lam,b2,j2,d,t,base_degree,stock,r,bins,weights):
    """Certify the product on one closed weight interval with a common board."""
    s = F(t,N)
    m0 = stock-base_degree**2
    variance = F(d,N)-s*s+(s-F(d,N))/m0
    b2, j2 = F(b2), F(j2)
    def base(q):
        return rank(q,h)-rank(q,h-v)
    def jump(q):
        return rank(q,h-v)-rank(q-1,h-v)
    slope = F(base(r+8)-base(r-8),16)
    coef = jump(r)/s
    start, stop = (r-lam*s).__floor__(), (r+lam*(1-s)).__floor__()
    require(start>0 and slope>0, 'nonnegative site orders')
    for q in range(start,stop+1):
        shift = q-r
        delta = F(r*min(abs(shift),abs(shift+1)),lam)**2
        require(base(q)<=base(r)+slope*shift+F(r,2)+b2*delta, 'base local envelope')
        require(jump(q)<=jump(r)+coef*F(shift,lam)+F(r,2)+j2*delta, 'increment envelope')
    cap_weight = ((r-3)*t+lam*N*variance).__floor__()
    eligible = 2*m0*t/(3*t+1+lam*N*variance)
    require(eligible>v*((cap_weight-1)//d)+h*base_degree, 'mixed Bezout, every group')
    least = None
    for i in range(bins):
        w = ((r-3)*t+lam*N*variance*i/bins).__floor__()
        z = variance*(i+1)/bins
        for D in weights:
            cost = (base(r)+F(r,2)+b2*r*r*z+coef*(s+F(D-d+1,N))
                    +(F(r,2)+j2*r*r*z)*(F(D,d)+v))
            surplus = slots(w,h,d)-slots(w-D,h-v,d)-N*cost
            least = surplus if least is None else min(surplus,least)
    require(least>0, 'adaptive quotient surplus')
    return least.__floor__()


def linear(d,t,primary,degree,cutoff,outside):
    r = 3000
    low,high = cutoff*d-1,primary-1
    cuts = {low,high+1}
    for j in range(2,degree+3):
        cuts.update(x for x in (j*d-1,j*d,j*t) if low<x<=high)
    cuts = sorted(cuts)
    least = None
    for left,stop in zip(cuts,cuts[1:]):
        a,b = (left-d+1)//d,left//d
        def mean(w,j):
            saved = 2*max(j*t-w,0) if outside else 0
            return F(N*(j*(j+1)+1)+a*w+b*(w-d+1)-a*b*d-saved,2*j*N)
        ends = (left,stop-1)
        js = {min(range(2,degree+2),key=lambda j: mean(w,j)) for w in ends}
        def surplus(h,w,j):
            cost = rank(r,h)-rank(r,h-1)+(rank(r,h-1)-rank(r-1,h-1))*mean(w,j)
            return slots(r*t,h,d)-slots(r*t-w,h-1,d)-N*cost
        best = max(min(surplus(h,w,j) for w in ends)
                   for j in js for h in range(r//20,r,r//20))
        require(best>0, f'linear factor near {left}, outside={outside}')
        least = best if least is None else min(least,best)
    return least.__floor__()


def certify(q,mult,extra,r0,rows):
    d = N//q-1
    t = isqrt(N*d)-extra
    P = r0*t
    b = (P-1)//(d-1)
    stock = N//40
    primary_surplus = slots(P,3,d)-N*rank(r0,3)
    require(primary_surplus>0, 'cubic primary')
    require(stock > b*((3000*t-1)//(d-1)), 'uniform linear Bezout')
    budget = mult*N
    base = 1+mult*q//2
    require(base+(2*base-2)*d<=budget, 'only linear factor')
    require(base-1+(2*base-4)*d+3*stock+b<=budget, 'linear with exterior')
    require((N-d)//(t-d)<stock, 'integral linear factor')
    margins = [linear(d,t,P,b,base+1,False),linear(d,t,P,b,base,True)]
    for v,h,lam,b2,j2,cutoff in rows:
        margins.append(adaptive(v,h,lam,b2,j2,cutoff,d,t,P,b,stock))
        if cutoff>v:
            size = cutoff-1
            bound = (2*size*v-v*v+size+d*(4*size*v-2*size-2*v*v)
                     +v*F(N-d,t-d))
            require(bound+3*stock+b<=budget, 'normalized curve budget')
    require(3*stock+b<budget, 'all groups small')
    print(f'1/{q}, budget {mult}n: {N-t:,} safe errors; primary surplus {primary_surplus:,}; '
          f'least surpluses {margins}.')


if __name__ == '__main__':
    for params in BOARDS:
        certify(*params)
