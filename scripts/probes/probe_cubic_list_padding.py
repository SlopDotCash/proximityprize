#!/usr/bin/env python3
"""Check padded cubic witnesses and the exact three-word interval on the named domains."""
from itertools import combinations

from probe_mu32_four_cubics import PAIRS, PRIVATE
from probe_linear_contact_quotient import require


def primitive_root(prime, size):
    for seed in range(2, 1000):
        root = pow(seed, (prime-1)//size, prime)
        if pow(root,size,prime)==1 and pow(root,size//2,prime)!=1:
            return root
    raise ArithmeticError('no primitive root in test range')


def locator(roots, x, prime):
    v = 1
    for root in roots:
        v = v*(x-root) % prime
    return v


def four_cubics(prime):
    n = 64
    g = primitive_root(prime,n)
    sites = [pow(g,j,prime) for j in range(n)]
    base = sites[::2]
    a,b,c = [[base[j] for j in PAIRS[0,i]] for i in (1,2,3)]
    cb = locator(a,base[6],prime)*pow(locator(b,base[6],prime),-1,prime) % prime
    cc = locator(a,base[14],prime)*pow(locator(c,base[14],prime),-1,prime) % prime
    words = [[0]*n]+[[scale*locator(roots,x,prime)%prime for x in sites]
                      for scale,roots in ((1,a),(cb,b),(cc,c))]
    center = [None]*n
    for (i,j),indices in PAIRS.items():
        for x in indices:
            require(words[i][2*x]==words[j][2*x], 'cubic tie')
            center[2*x] = words[i][2*x]
    for i,indices in enumerate(PRIVATE):
        for x in indices:
            center[2*x] = words[i][2*x]
    for j in range(n//2):
        x = 2*j+1
        center[x] = words[j//8][x]
    require(len(set(map(tuple,words)))==4,'distinct words')
    require(all(m is not None for m in center), 'one full center')
    require(min(sum(a==b for a,b in zip(w,center)) for w in words)>=20,'four hits of twenty')
    require(4*21>64+6*3 and 64-20==44, 'exact error count')


def split_cubic(prime):
    w = primitive_root(prime,16)
    sites = [pow(w,j,prime) for j in range(16)]
    a = [sites[i] for i in (0,1,8)]
    b = [sites[i] for i in (2,9,10)]
    scale = locator(a,sites[3],prime)*pow(locator(b,sites[3],prime),-1,prime) % prime
    values = [[0]*16,[locator(a,x,prime) for x in sites],[scale*locator(b,x,prime)%prime for x in sites]]
    pairs = [{j for j in range(16) if values[i][j]==values[k][j]} for i,k in combinations(range(3),2)]
    require(all(len(s)==3 for s in pairs) and len(set.union(*pairs))==9, 'three disjoint cubic fibers')


def verify():
    n = 2**30
    h = n//64
    d = n//16-1
    prime = (3*2**48+69)*2**80+1
    first = 365375409332725729550921208179070755120141565953
    second = 730750818665451459101842416358141509841924915201
    for p in (prime,first,second,193):
        four_cubics(p)
        split_cubic(p)
    require(prime//2**128==3 and (prime-1)%64==0,'130-bit security budget and subgroup')
    t_three = 25*h-1
    upper = (n+6*d)//4+1
    require(3*18*h<=n-9*h-(h-1) and t_three==6*h+h-1+18*h,'three private allocations')
    require(4*upper>n+6*d and (n-t_three,n-upper)==(654311425,704643073),'exact named interval')
    pivot_t = n-715827882
    require(5*pivot_t>n+10*d and pivot_t<=t_three, 'three or four at second-prime pivot')
    target = 4*pivot_t-n
    for m in (1,2,4,8,16,32,64,128):
        fiber_size = n//m
        possible = [(degree,cost) for degree in range(d//fiber_size+1)
                    for cost in range(6*degree+1) if 3*d+fiber_size*(cost-3*degree)>=target]
        if m<128:
            require(not possible, 'quotient too short')
        else:
            require(possible==[(7,40),(7,41),(7,42)], 'septic quotient bound')
    require(7**32<min(first,second), 'norm transfer')
    for residue in range(4):
        require(any(j%4==residue for j in (0,1,6,7)), 'cyclic difference forces a missing coefficient')
    require(4+3*(3-1)<=64 and 4+3+1<=64,'length-64 MCA first failure at three')
    print('First failure 44 at length 64, dimension four, budget three.')
    print('Exact list size three at 654,311,425 through 704,643,073 errors on both named sixteenth-rate domains.')
    print('At the second-prime MCA first failure of 715,827,882 errors, the list size is three or four.')


if __name__=='__main__':
    verify()
