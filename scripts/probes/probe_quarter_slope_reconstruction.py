#!/usr/bin/env python3
"""Verify 36 literal four-head labels on a specified length-16 domain."""
from itertools import combinations
from math import prod

P = 730750818665451459101842416358141509841924915201
MAPS = ((8, 9, 1, 2), (1, 3, 4, 5), (3, 8, 5, 1))
SIGNS = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))


def square_root(a):
    """Tonelli-Shanks with the known two-adic valuation of the named prime."""
    q = (P-1) >> 30
    assert q % 2 and pow(a, (P-1)//2, P) == 1
    z = 2
    while pow(z, (P-1)//2, P) == 1:
        z += 1
    c, t, r, m = pow(z, q, P), pow(a, q, P), pow(a, (q+1)//2, P), 30
    while t != 1:
        s, i = t, 0
        while s != 1:
            s, i = s*s % P, i+1
        assert 0 < i < m
        b = pow(c, 1 << (m-i-1), P)
        c, t, r, m = b*b % P, t*b*b % P, r*b % P, i
    assert r*r % P == a % P
    return r


def double_sites(j, k, sign):
    a,b,c,d = MAPS[j]
    e,f,g,h = MAPS[k]
    coeff2 = a*g+sign*e*c
    coeff1 = a*h+b*g+sign*(e*d+f*c)
    coeff0 = b*h+sign*f*d
    root = square_root(coeff1**2-4*coeff2*coeff0)
    return [(-coeff1+eps*root)*pow(2*coeff2, -1, P) % P for eps in (-1, 1)]


def heads(x):
    ps = [(a*x+b) % P for a,b,_,_ in MAPS]
    qs = [(c*x+d) % P for _,_,c,d in MAPS]
    def row(ps, qs, signs):
        return sum(signs[i]*ps[i]*prod(qs[j] for j in range(3) if j != i)
                   for i in range(3)) % P
    return tuple((row(ps, qs, sign), row(qs, ps, sign)) for sign in SIGNS)


def interpolate(nodes, values, x):
    return sum(values[i] * prod((x-y)*pow(z-y, -1, P) % P
                                for y in nodes if y != z)
               for i,z in enumerate(nodes)) % P


def main():
    assigned = {}
    for j,k in combinations(range(3), 2):
        i = 3-j-k
        for sign, owners in ((1, (0, i+1)), (-1, (j+1,k+1))):
            for x in double_sites(j, k, sign):
                assert x not in assigned
                assigned[x] = owners
    for i,x in enumerate((1, 2, 3, 4)):
        assert x not in assigned
        assigned[x] = (i,)
    assert len(assigned) == 16
    received = {x: heads(x)[owners[0]] for x,owners in assigned.items()}
    for x,owners in assigned.items():
        assert tuple(i for i,w in enumerate(heads(x)) if w == received[x]) == owners
    labels = set()
    for i in range(4):
        core = [x for x,owners in assigned.items() if i in owners]
        assert len(core) == 7
        nodes = core[:4]
        for x in assigned.keys()-set(core):
            a,b = heads(x)[i]
            u,v = received[x]
            gamma = (u-a)*pow(b-v, -1, P) % P
            assert gamma not in labels
            labels.add(gamma)
            support = core+[x]
            folds = [(received[y][0]+gamma*received[y][1]) % P for y in nodes]
            assert all(interpolate(nodes, folds, y) == (received[y][0]+gamma*received[y][1]) % P
                       for y in support)
            row_pair = tuple(interpolate(nodes, [received[y][j] for y in nodes], x)
                             for j in range(2))
            assert row_pair == (a,b) and row_pair != (u,v)
    assert len(labels) == 36
    print('n=16, k=4, e=8, 12 double sites, 4 singleton sites, 36 distinct literal bad scalars')


if __name__ == '__main__':
    main()
