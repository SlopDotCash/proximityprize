#!/usr/bin/env python3
"""Certify a first-prime eighth-rate list bound using the quartic discriminant."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import isqrt

from probe_joint_list_contact_boards import N, adaptive, linear, rank, require, slots


def discriminant_support(degree):
    """Compute the coefficient exponents of the discriminant by its Sylvester matrix."""
    size = 2*degree-1
    determinant = defaultdict(int)
    for perm in permutations(range(size)):
        exponents = [0]*(degree+1)
        coefficient = 1
        for row,column in enumerate(perm):
            if row<degree-1:
                index = column-row
                if not 0<=index<=degree:
                    break
            else:
                index = column-(row-degree+1)+1
                if not 1<=index<=degree:
                    break
                coefficient *= index
            exponents[index]+=1
        else:
            sign = (-1)**sum(x>y for i,x in enumerate(perm) for y in perm[i+1:])
            exponents[-1]-=1
            determinant[tuple(exponents)]+=sign*coefficient
    return [e for e,c in determinant.items() if c]


def verify():
    d = N//8-1
    t = isqrt(N*d)-10_000_000
    primary = 8*t
    b = (primary-1)//(d-1)
    stock = N//40
    primary_surplus = slots(primary,3,d)-N*rank(8,3)
    require(primary_surplus>0 and stock>b*((3000*t-1)//(d-1)), 'primary and linear Bezout')
    adaptive_surplus = [adaptive(v,h,l,b2,j2,3,d,t,primary,b,stock) for v,h,l,b2,j2 in
                        ((2,500,4999,'6.4','.25'),(3,600,4857,'9','.35'))]
    high = linear(d,t,primary,b,6,False)
    monomials = discriminant_support(4)
    require(len(monomials)==16 and all(min(m)>=0 and sum(m)==6 and
            sum(i*p for i,p in enumerate(m))==12 for m in monomials), 'quartic discriminant')
    costs = [min(sum(e*max(o-j-1,int(o>=j+1)) for j,e in enumerate(m))
                 for m in monomials) for o in range(7)]
    require(costs==[0,0,1,3,7,12,18] and all(c>=2*o-3 for o,c in enumerate(costs)),
            'local discriminant order')
    r,h = 3000,1500
    def margin(w):
        mean = F(3,2)+F(6*(w-d+1)-12*d,2*N)
        local = rank(r,h)-rank(r,h-1)+(rank(r,h-1)-rank(r-1,h-1))*mean
        return slots(r*t,h,d)-slots(r*t-w,h-1,d)-N*local
    low = min(margin(w) for w in (5*d-1,6*d-2)).__floor__()
    require(low>0, 'quartic discriminant quotient')
    quad = 2*2*2-2**2+2+d*(4*2*2-2*2-2*2**2)+2*F(N-d,t-d)
    require(quad+3*stock+b<=N and 5+7*d+3*stock+b<=N, 'residual factor budgets')
    require(F(N-d,t-d)<stock and 3*stock+b<=N, 'integral and small groups')
    print(f'{N-t:,} safe errors at budget {N:,}; primary surplus {primary_surplus:,}.')
    print(f'Adaptive surpluses {adaptive_surplus}; high linear {high:,}; quartic {low:,}.')


if __name__=='__main__':
    verify()
