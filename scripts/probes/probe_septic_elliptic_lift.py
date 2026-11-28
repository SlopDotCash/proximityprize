#!/usr/bin/env python3
"""Exhaust the rational elliptic order-seven kernels over F_127 and their relabelings on mu_128."""
from collections import Counter
from functools import cache
from itertools import combinations

from probe_linear_contact_quotient import require


P = 127
NAMED = 730750818665451459101842416358141509841924915201
INVERSE = [0]+[pow(x,-1,P) for x in range(1,P)]
ROOT = pow(37,(NAMED-1)//128,NAMED)
GRID = tuple(pow(ROOT,j,NAMED) for j in range(128))
ALL = (1<<128)-1
EVEN = ALL//3
SQUARE_ROOT = {y*y%P:y for y in range(P)}


def add(left,right,a):
    if left is None:
        return right
    if right is None:
        return left
    x,y = left
    u,v = right
    if x==u and (y+v)%P==0:
        return None
    slope = (3*x*x+a)*INVERSE[2*y%P] if x==u else (v-y)*INVERSE[(u-x)%P]
    z = (slope*slope-x-u)%P
    return z,(slope*(x-z)-y)%P


def multiple(n,point,a):
    value = None
    while n:
        if n%2:
            value = add(value,point,a)
        point = add(point,point,a)
        n //= 2
    return value


def elliptic_families():
    visited = set()
    families = []
    for a in range(P):
        for b in range(P):
            if (a,b) in visited or not (4*a**3+27*b*b)%P:
                continue
            visited.update((a*v**4%P,b*v**6%P) for v in range(1,P))
            points = [(x,SQUARE_ROOT[y2]) for x in range(P)
                      if (y2:=(x**3+a*x+b)%P) in SQUARE_ROOT]
            order = 1+sum(2 if y else 1 for x,y in points)
            if order%7:
                continue
            while order%7==0:
                order //= 7
            kernels = set()
            for point in points:
                t = multiple(order,point,a)
                if t is None:
                    continue
                while (u:=multiple(7,t,a)) is not None:
                    t = u
                kernels.add(tuple(sorted(multiple(j,t,a)[0] for j in (1,2,3))))
            for kernel in kernels:
                fibers = {}
                for x in range(P):
                    if x not in kernel:
                        value = x+sum(2*(3*c*c+a)*INVERSE[(x-c)%P]
                                      +4*(c**3+a*c+b)*INVERSE[(x-c)%P]**2 for c in kernel)
                        fibers.setdefault(value%P,[]).append(x)
                full = [v for v in fibers.values() if len(v)==7]
                if len(full)>=3:
                    families.append(full)
    return families


def cayley_exponents():
    units = [((x*x-1)*INVERSE[(x*x+1)%P]%P,-2*x*INVERSE[(x*x+1)%P]%P)
             for x in range(P)]
    for a,b in units:
        log = {(1,0):0}
        u,v = 1,0
        for j in range(1,128):
            u,v = (u*a-v*b)%P,(u*b+v*a)%P
            log[u,v] = j
        if len(log)==128:
            return [log[unit] for unit in units]
    raise ArithmeticError('no generator')


@cache
def evaluations(support):
    values = [1]*128
    for j in support:
        values = [v*(x-GRID[j])%NAMED for v,x in zip(values,GRID)]
    return values


def verify():
    require(len(set(GRID))==128,'primitive named root')
    families = elliptic_families()
    require(Counter(map(len,families))=={6:5,7:5,8:16,9:10,10:10},'all source families')
    exps = cayley_exponents()
    masks = [1<<j for j in exps]
    count = 0
    maximum = 0
    for a in range(1,64):
        for b in range(P):
            labels = [(a*x+b)%P for x in range(P)]
            marked = [masks[x] for x in labels]
            for family in families:
                by_parity = [[],[]]
                for f in family:
                    bits = sum(marked[x] for x in f)
                    diff = bits^((bits<<64)&ALL)^(bits>>64)
                    if not diff&EVEN:
                        by_parity[0].append(f)
                    if not diff&(ALL^EVEN):
                        by_parity[1].append(f)
                for group in by_parity:
                    for one,two in combinations(group,2):
                        count += 1
                        u,v = (evaluations(tuple(sorted(exps[labels[x]] for x in f))) for f in (one,two))
                        counts = Counter(y*pow(z,-1,NAMED)%NAMED for y,z in zip(u,v) if y and z)
                        maximum = max(maximum,max(counts.values()))
    require(count==1599 and maximum<=4,'all compatible support pairs')
    print(f'{len(families)} isogeny families, 8,001 projective relabelings each; '
          f'{count:,} pairs survive parity, maximum named-field third fiber {maximum}.')


if __name__=='__main__':
    verify()
