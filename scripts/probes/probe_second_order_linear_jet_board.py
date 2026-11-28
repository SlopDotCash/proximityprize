#!/usr/bin/env python3
"""Independent local-rank enumeration and finite second-derivative boards."""
from collections import defaultdict
from fractions import Fraction
from math import comb

from probe_quarter_coset_lists import require
from probe_sixteenth_list_adaptive_quotient import rank


def staircase(order, cap):
    return {(i,j) for j in range(min(cap,order//2)+1)
            for i in range(order+cap-3*j+1)}


def second_rank(order, cap_a, cap_b):
    top = staircase(order-1,cap_b)
    extra = {(i,j+1) for i,j in top}-staircase(order-1,cap_a)
    return rank(order,cap_a)+rank(order-1,cap_b)+len(extra)


def direct_rank(order, cap_a, cap_b, prime):
    # Expand every relevant monomial directly in u,z,w,eta; reduce sparse
    # columns by elementary field elimination without the staircase formula.
    pivots = defaultdict(dict)
    for ell,cap in ((0,cap_a),(1,cap_b)):
        for i in range(order):
            for j in range(order-i):
                for k in range(cap+1):
                    block = pivots[(i+j-ell,j+k+ell)]
                    column = {}
                    for a in range(k+1):
                        for b in range(ell+1):
                            if i+j+a+b < order:
                                index = (i+j+a+b,j+k-a,a+ell-b,b)
                                column[index] = (comb(k,a)*comb(ell,b)*2**(ell-b))%prime
                    column = {index:value for index,value in column.items() if value}
                    while column:
                        key = min(column)
                        coeff = column[key]
                        if key not in block:
                            inverse = pow(coeff,-1,prime)
                            block[key] = {m:c*inverse%prime for m,c in column.items()}
                            break
                        for m,c in block[key].items():
                            new = (column.get(m,0)-coeff*c)%prime
                            if new:
                                column[m]=new
                            else:
                                column.pop(m,None)
    return sum(map(len,pivots.values()))


def source(weight, cap, d):
    result = 0
    for k in range(cap+1):
        a = weight-(d-1)*k
        if a<=0:
            break
        m = (a+d-1)//d
        result += m*a-d*m*(m-1)//2
    return result


def boards():
    n = 2**30
    for denom,r,ha,hb,errors in [
            (2,16,5,2,324_179_110),(4,16,8,5,561_214_324),
            (8,16,10,7,723_318_701),(16,16,11,8,833_476_786)]:
        d,t = n//denom-1,n-errors
        cost = second_rank(r,ha,hb)
        def surplus(t):
            return source(r*t,ha,d)+source(r*t-d+2,hb,d)-n*cost
        require(surplus(t)>0 and surplus(t-1)<=0, 'first positive board')
        b = (r*t-1)//(d-2)
        L = (2*d-3)*(b-1)+1
        ratio = Fraction(n-d,t-d)
        first_order = 2*b*ha-ha*ha+b+d*(4*b*ha-2*b-2*ha*ha)+ha*ratio
        bound = L**2*ratio**2+b*b+first_order
        budget = (bound/n**2).__ceil__()
        print(f'1/{denom}: {errors:,} errors; local cost {cost}, surplus {surplus(t):,}, '
              f'b={b}, L={L:,}, bound {budget}n².')


def literal_fields():
    n = 2**30
    for budget,offset,witness in [(2810,53,3),(2289,24,7),(1889,43,5),(1657,30,3)]:
        prime = budget*2**188+offset*2**110+1
        require(prime//2**128 == budget*n**2, 'literal field budget')
        require((prime-1) % 2**110 == 0 and (2**110+1)**2 > prime, 'prime divisor floor')
        require(pow(witness,(prime-1)//2,prime)==prime-1, 'primality certificate')
        require(pow(pow(witness,(prime-1)//n,prime),n//2,prime)==prime-1, 'order-n grid')

    for q,r,ha,hb,errors,expected in [(2,16,5,2,324_179_110,234),
            (4,17,8,6,561_917_629,2199),(8,19,11,8,724_787_769,12524),
            (16,20,14,11,834_849_894,31168)]:
        d,t = n//q-1,n-errors
        cost = n*second_rank(r,ha,hb)
        def surplus(t):
            return source(r*t,ha,d)+source(r*t-d+2,hb,d)-cost
        require(surplus(t)==expected and surplus(t-1)<=0, 'common field primary')
        b = (r*t-1)//(d-2)
        degree = (2*d-3)*(b-1)+1
        ratio = Fraction(n-d,t-d)
        bound = degree**2*ratio**2+b*b+2*b*ha-ha*ha+b+d*(4*b*ha-2*b-2*ha*ha)+ha*ratio
        require(bound <=2810*n**2, 'common field list budget')
        print(f'1/{q}: {errors:,} safe errors on the same prime grid at the 128-bit budget.')


if __name__=='__main__':
    checks = 0
    for r in range(1,9):
        for ha in range(6):
            for hb in range(ha+1):
                for p in (17,101):
                    require(direct_rank(r,ha,hb,p)==second_rank(r,ha,hb), 'local jet matrix rank')
                    checks += 1
    print(f'{checks} independently reduced finite-field jet matrices passed.')
    boards()
    literal_fields()
