#!/usr/bin/env python3
"""Half-rate certificate with the second contact moment of a quadratic factor."""
from fractions import Fraction as F
from math import isqrt

import probe_half_list_coefficient_derivatives as base
from probe_linear_contact_quotient import rank, require
from probe_sixteenth_list_quotient_jets import upper_sqrt

N, D = base.N, base.D
T = isqrt(N*D)-900_000
S = F(T,N)
R = 40_000
LARGE = 900_000
P = 11*T
DEG = (P-1)//(D-1)
SIGMA = upper_sqrt(F(D,N)-S*S+(S-F(D,N))/(LARGE-DEG**2))


def margin(weight,mean,v,h):
    return (base.fast_slots(R*T,h)-base.fast_slots(R*T-weight,h-v)
            -N*(rank(R,h)-rank(R,h-v)+(rank(R,h-v)-rank(R-1,h-v))*mean))


def linear_limits(w,a,b):
    e = w-D+1
    result = [F(a*w+b*e-a*b*D,N)]
    for j in range(a+1):
        cost = F(e-j*D,N)
        if j<a:
            height = max(base.content_and_order(o,a,j)[1] for o in range(b+2))
            # The imported pointwise rows use the preceding certificate's mean.
            cost += (SIGMA/2+base.S-S)*height
        result.append(cost)
    result.append((S+F(e,N)+(1-S)*a/2+SIGMA*(b+1))/(S+(1-S)/2))
    return result


def linear(a,b,left,right):
    mid = (left+right)//2
    rows = base.contact_values(a,b+1)
    coeff,bias = base.dual_proposal(rows,linear_limits(mid,a,b))
    def mean(w):
        return bias+sum(c*x for c,x in zip(coeff,linear_limits(w,a,b)))
    h = max(range(1,R,R//180),key=lambda cap:margin(mid,mean(mid),1,cap))
    surplus = min(margin(w,mean(w),1,h) for w in (left,right))
    if surplus>0:
        return 1,surplus.__floor__()
    require(left<right,'linear interval loses positivity')
    count1,min1 = linear(a,b,left,mid)
    count2,min2 = linear(a,b,mid+1,right)
    return count1+count2,min(min1,min2)


def quadratic(left,right):
    a,b = (left-2*(D-1))//D,left//D
    best = 0
    for c in range(2,b+5):
        for divisor in (40,60,80,100,150,200,300,500,750,1000):
            theta = F(1,divisor)
            def mean(w):
                intersection = F(a*w+b*(w-2*(D-1))-a*b*D,N)
                return ((S+F(w-D+1,N)+SIGMA**2/(2*theta)
                         +theta*(intersection+4+4*(c-2)+(c-2)**2)/2)
                        /(S+theta*(c-2)))
            m1,m2 = mean(left),mean(right)
            for cap in range(R//100,R,R//40):
                best = max(best,min(margin(left,m1,2,cap),margin(right,m2,2,cap)))
    require(best>0,'quadratic interval loses positivity')
    return best.__floor__()


def verify():
    require(S<=base.S,'imported linear pointwise rows dominate the new ones')
    primary = base.fast_slots(P,2)-N*rank(11,2)
    require(primary>0 and DEG*((R*T-1)//(D-1))<LARGE,'primary and mixed Bezout')
    def ordinary(w):
        return 1+F(w-D+1,T)+(F(w,D)+1)*SIGMA/(2*S)
    high = max(min(margin(w,ordinary(w),1,h) for w in (13*D,P-1))
               for h in range(1,R,R//140)).__floor__()
    require(high>0,'large weight linear factors')
    cut_q = sorted({2*(D-1),P}|{j*D-i for j in range(2,P//D+2) for i in (0,2)
                                if 2*(D-1)<=j*D-i<=P})
    quad = min(quadratic(l,r-1) for l,r in zip(cut_q,cut_q[1:]))
    cut_l = sorted({D-1,13*D}|{j*D-i for j in range(1,14) for i in (0,1)
                               if D-1<=j*D-i<=13*D})
    lows = [linear(a,l//D,l,r-1) for l,r in zip(cut_l,cut_l[1:])
            for a in range((l-D+1)//D+1)]
    print(f'{N-T:,} safe errors, list size at most {2*LARGE+DEG:,}, '
          f'primary surplus {primary:,}.')
    print(f'{len(cut_q)-1} quadratic intervals, minimum surplus {quad:,}. '
          f'{sum(n for n,_ in lows)} linear intervals, minimum {min(m for _,m in lows):,}; '
          f'high linear surplus {high:,}.')


if __name__=='__main__':
    verify()
