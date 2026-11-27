#!/usr/bin/env python3
"""Check weighted Hermite agreement coordinates and the second-prime quarter list bound."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

from probe_quarter_coset_lists import evaluate, poly_mul, require
from probe_quarter_list_moving_jets import verify


def certificate():
    n = 2**30
    d = n//4-1
    t = 2*d-17
    r = n-2*t
    words = 2*n+1
    c = F(t-d, d)
    spectral = 1+F(words*(n*d-t*t), n*(t-d))
    energy = 2*spectral*(spectral-1)*(spectral+1)**2
    require(energy < words, 'square mass below twice the number of rows')

    def edges(overlap):
        mu = 1-F(overlap, d)
        weak = (energy+2*words*(1-c*c))/(1-mu*mu)
        return (c*c*words-weak)/2, spectral**2/mu**2

    tight, degree = edges(63_100_000)
    loose, _ = edges(140_000_000)
    require(tight > 942_196 and degree < 35_933, 'two disjoint tight anchors')
    require(loose > 496_524_830, 'number of loose pairs')
    holes = r+63_100_000-1
    require(n-2*holes-(r+140_000_000-1) > 3*d, 'pencil determinant')
    max_e = 218_000_000
    tight_floor = 942_196

    def value_johnson(e):
        u = F(e-4, 2)
        return tight_floor*((e-holes)**2-e*u)-e*(e-holes-u)

    require(value_johnson(max_e)>0 and value_johnson(max_e)>value_johnson(max_e-1),
            'positive increasing quadratic beyond maximum exceptional count')
    require(tight_floor > 1 and max_e > holes, 'positive leading coefficient and hits')
    sections = 496_000_000
    require(1+3*max_e//2 < sections, 'negative dot product simplex bound')
    min_e, split_e, large_e = 20_000, 4_000_000, 110_000_000
    numerator = 4*r-8
    delta = numerator+1
    require(numerator*(min_e+delta) <= 73*(2*min_e-delta) and numerator<146,
            'uniform inner product bound')
    require(2*73**2 <= min_e and F(74**2,73)/(1-F(73**2,min_e)) < 103,
            'positive cubic coefficients and uniform bound')
    require(103*(split_e+delta) < sections, 'cubic excludes all small lengths')
    require(4*(large_e+delta+1) <= sections, 'medium trace subset available')
    require(4*73*F(split_e+1,split_e-73)<293, 'medium spectral radius')
    require(8*split_e>293*295**2, 'medium trace contradiction')
    require((11*(max_e+delta+1)+4)//5 < 480_000_000, 'large trace subset available')
    require(73*F(11*(large_e+1)+5,5*(large_e-73)) < 162, 'large spectral radius')
    require(F(11,25)*(large_e+1) > 162*164**2, 'large trace contradiction')
    controls = verify(n, min_e, sections, 82, 83, 16, 4)
    require(controls == (536_850_914, 6_708_575_990, 7_998_800, 24_800_000),
            'moving sections and differential Bezout')
    print(f'{n-t:,} safe errors, {int(tight):,} tight pairs, {int(loose):,} pencil parameters')


def field_control():
    p = 17
    roots = (1,1,2,3,4,5,6,8)
    xs = range(p)

    def factor(parts):
        poly = [1]
        for a in parts:
            poly = poly_mul(poly, [1, -a], p)
        return poly

    def derivative(f):
        return [(j*c) % p for j,c in enumerate(f) if j]

    def minus(f, g):
        return [(a-b) % p for a,b in zip(f,g)]

    def add(f, g):
        return [(a+b) % p for a,b in zip(f,g)]

    def factors():
        for indices in combinations(range(len(roots)),4):
            left = [a for i,a in enumerate(roots) if i in indices]
            right = [a for i,a in enumerate(roots) if i not in indices]
            # A=X, B=-1. Each factor is Af-B and equals 1 at zero.
            yield tuple(sorted((tuple(factor(left)[1:]), tuple(factor(right)[1:]))))

    pairs = sorted(set(factors()))
    N = factor(roots)
    base = add(*pairs[0])
    product = poly_mul(*pairs[0], p)
    params = [minus(add(f,g),base)[1:] for f,g in pairs]
    require(len(set(map(tuple,params))) == len(pairs), 'distinct parameters')
    cases = Counter()
    for x in xs:
        get = lambda f: evaluate(f,x,p)
        A, B, S, P, Nx = x, p-1, get(base), get(product), get(N)
        values = [(get(f),get(g),get(u),get(derivative(u))) for (f,g),u in zip(pairs,params)]
        for y in xs:
            ordinary = Nx == 0 and (A*y-B)%p == 0
            coeff = (B-A*y)%p
            if coeff:
                w = ((S*y-y*y-P)*pow(coeff,-1,p))%p
                double = (S+A*w-2*y)%p == 0
            else:
                w, double = None, False
            for f,g,u,du in values:
                hits = int(f==y)+int(g==y)
                if ordinary:
                    require(hits>=1, 'ordinary baseline')
                    if hits==2:
                        require(get(derivative(N))==0 and (S+A*u-2*y)%p==0, 'ordinary extra mark')
                        cases['ordinary double'] += 1
                elif w is None:
                    require(hits==0, 'exceptional site with impossible target')
                    cases['impossible'] += 1
                else:
                    require(hits==(1+double)*int(u==w), 'weighted exceptional mark')
                    if hits==2:
                        FX = (2*(S+A*w)*(get(derivative(base))+w)-4*get(derivative(product)))%p
                        FZ = 4*(A*y-B)%p
                        require(FZ and (FX+FZ*du)%p==0, 'exceptional Hermite derivative')
                        cases['pole double' if A==0 else 'finite double'] += 1
                    elif hits==1:
                        cases['simple'] += 1
    require(all(cases[key] for key in ('ordinary double','impossible','simple','finite double','pole double')),
            f'all local rules exercised: {cases}')
    print(f'All {len(pairs)} factorizations and all {p*p} site-symbol choices over F_{p} passed.')


if __name__ == '__main__':
    certificate()
    field_control()
