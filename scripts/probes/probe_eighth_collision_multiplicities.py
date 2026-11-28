#!/usr/bin/env python3
"""First-prime eighth-rate bound with simple radial and two-slope collision classes."""

from fractions import Fraction as F

from probe_eighth_coupled_cofactor import D, degree_six_exterior, finish, individual_exterior, large_products
from probe_linear_contact_quotient import N, require, upper_sqrt


def verify():
    s = F(171,500)
    t = (N*s).__ceil__()
    rows = [(2,500,4999,'6.255','.232'), (3,600,4857,'8.861','.318'), (4,600,5000,'12.527','.208')]
    large_products(t,rows)
    individual_exterior(s,t)
    excess = F(104,1000)
    group = degree_six_exterior(s,t,excess)
    beta, offset = F(83,100), F(21,1000)
    rate = F(D,N)
    require(1-(1-upper_sqrt(rate+F(1,group)))**4<=beta, 'exceptional true visit')
    require(F(2,3)<=beta**2 and F(1,2)<=beta**2, 'weighted collision classes')
    q = F(46,1000)
    slope = 5*(1-q)**4
    require(slope<=5*beta and 1-(1-q)**5-q*slope<=offset, 'simple radial visit')
    eta = rate-s*s+(1+2*excess)/group
    require((1-s)**8*eta<=beta**2*excess*s*s, 'decreasing coupled rank')
    dim = int(N*(1-(1-s)**5+5*beta*upper_sqrt(excess*eta)+offset*excess+10*(1+excess)/group))+6
    finish(t,group,dim,(1_072_464_183,1_276_641,841))
    require(N-t==706_522_120, 'named error count')
    print(f'First-prime eighth-rate list budget is safe through {N-t:,} errors.')


if __name__ == '__main__':
    verify()
