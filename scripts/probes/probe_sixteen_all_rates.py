#!/usr/bin/env python3
"""Verify every coordinate of the four budget-three witnesses over a quartic extension."""

from math import isqrt

P = 5_700_000_067
ZERO = (0,0,0,0)
ONE = (1,0,0,0)
Z = (0,1,0,0)
TRACE = pow(P-2,(P+1)//4,P)


def add(a,b):
    return tuple((x+y)%P for x,y in zip(a,b))


def sub(a,b):
    return tuple((x-y)%P for x,y in zip(a,b))


def mul(a,b):
    coeff = [0]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            coeff[i+j] += x*y
    for k in range(6,3,-1):
        coeff[k-2] += TRACE*coeff[k]
        coeff[k-4] += coeff[k]
    return tuple(x%P for x in coeff[:4])


def check():
    assert all(P%j for j in range(2,isqrt(P)+1))
    assert P**4//2**128==3 and P%16==3 and TRACE**2%P==P-2
    x = [ONE]
    for _ in range(15):
        x.append(mul(x[-1],Z))
    assert len(set(x))==16 and x[8]==sub(ZERO,ONE) and mul(x[15],Z)==ONE

    def locator(y,support):
        value = ONE
        for j in support:
            value = mul(value,sub(y,x[j]))
        return value

    def check_center(rows,owners,least):
        assert len(set(map(tuple,rows)))==len(rows)
        center = [rows[i][j] for j,i in enumerate(owners)]
        counts = [sum(a==b for a,b in zip(row,center)) for row in rows]
        assert min(counts)>=least
        return counts

    lp = lambda y: locator(y,(0,1,8))
    lq = lambda y: mul(x[2],locator(y,(2,9,10)))
    scale = add(add(x[2],x[4]),x[6])
    quartet = [[ZERO]*16,list(map(lp,x)),list(map(lq,x)),
               [mul(scale,locator(y,(1,4,12))) for y in x]]
    owner = [0,0,0,1,0,1,1,1,0,0,0,1,0,2,3,2]
    assert check_center(quartet,owner,8)==[8]*4
    # The same cyclic identities provide three words at eleven agreements in degree seven.
    remaining = sorted(set(range(16))-{0,1,8,2,9,10,3,5,7})
    common,private = remaining[:4],remaining[4:]
    trio = [[mul(locator(y,common),row[j]) for j,y in enumerate(x)] for row in quartet[:3]]
    owner = [1 if j in (3,5,7) else 0 for j in range(16)]
    for i,j in enumerate(private):
        owner[j] = i
    assert check_center(trio,owner,11)==[11]*3

    labels = (0,1,3,7)
    lines = [[add(mul(x[a],y),x[-a%16]) for y in x] for a in labels]
    intersections = {(-a-b)%16:i for i,a in enumerate(labels) for b in labels[i+1:]}
    assert len(intersections)==6
    unused = sorted(set(range(16))-intersections.keys())
    owner = [intersections.get(j,0) for j in range(16)]
    for j,site in enumerate(unused):
        owner[site] = j%4
    assert sorted(check_center(lines,owner,5))==[5,5,6,6]
    common,private = unused[:6],unused[6:]
    septics = [[mul(locator(y,common),row[j]) for j,y in enumerate(x)] for row in lines]
    for i,j in enumerate(private):
        owner[j] = i
    assert check_center(septics,owner,10)==[10]*4
    constants = [[y]*16 for y in x[:4]]
    assert check_center(constants,[j%4 for j in range(16)],4)==[4]*4

    for k,first in [(1,12),(2,11),(4,8)]:
        assert 4*(16-first+1)>16+6*(k-1)
    for k in (1,2,4,8):
        assert k+6<=16 and k+4<=16
    print(f'Field cardinality {P**4}, 128-bit budget three, primitive grid of size sixteen.')
    print('First MCA failures [3, 3, 3, 3]; first list failures [6, 8, 11, 12] in decreasing rate.')


if __name__=='__main__':
    check()
