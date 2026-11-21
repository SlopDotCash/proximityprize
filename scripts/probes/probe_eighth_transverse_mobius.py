#!/usr/bin/env python3
"""Check the named-field four-head allocation, Möbius maps and collision budget."""
from collections import Counter
from itertools import combinations
from math import prod

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import PRIME, GENERATOR, cubic

PRODUCTION = 2**30
PAIR = {0: "01", 2: "01", 16: "01", 4: "02", 18: "02", 20: "02",
        6: "12", 10: "12", 14: "12"}
VARIABLE = (5, 7, 8, 9, 11, 12, 13, 15, 17, 19, 21, 22, 23)
OWNERS = {"01": (0, 1, 3), "02": (0, 2), "12": (1, 2),
          "root": (0, 1, 2, 3), "u": (2, 3), "v": (2, 3),
          "a": (0,), "b": (1,), "c": (2,), "d": (3,)}


def allocate(n):
    """Each interval (j,start,stop,label) occupies exponents j+32i."""
    s = n//32
    require(s >= 4 and s % 4 == 0 and 32*s == n, "integral allocation")
    private = 19*s//4+1
    fourth = 31*s//4-1
    segments, free = [], []
    for j in range(32):
        if j in PAIR:
            segments.append((j, 0, s, PAIR[j]))
        elif j in (1, 3):
            segments.append((j, 0, 1, "u" if j == 1 else "v"))
            free.append((j, 1, s))
        elif j == 31:
            segments.append((j, 0, s-2, "root"))
            free.append((j, s-2, s))
        elif j not in VARIABLE:
            free.append((j, 0, s))
    stop2 = private-2
    stop4 = stop2+fourth
    for i, j in enumerate(VARIABLE):
        a = max(0, min(s, stop2-i*s))
        b = max(0, min(s, stop4-i*s))
        segments.extend([(j, 0, a, "c"), (j, a, b, "d")])
        free.append((j, b, s))
    left = private
    for j, lo, hi in free:
        mid = min(hi, lo+left)
        segments.extend([(j, lo, mid, "a"), (j, mid, hi, "b")])
        left -= mid-lo
    require(left == 0, "head zero filled")
    segments = sorted(sg for sg in segments if sg[1] < sg[2])
    for j in range(32):
        blocks = [(lo, hi) for t, lo, hi, tag in segments if t == j]
        require(blocks[0][0] == 0 and blocks[-1][1] == s and all(
            b == c for (_, b), (c, _) in zip(blocks, blocks[1:])), "partition")
    counts = Counter()
    for _, lo, hi, tag in segments:
        for h in OWNERS[tag]:
            counts[h] += hi-lo
    require(list(counts.values()) == [47*s//4-1]*4, "four balanced cores")
    return segments


def quotient(n):
    p = PRIME
    g = pow(GENERATOR, PRODUCTION//n, p)
    require(pow(g, n//2, p) == p-1, "domain order")
    omega = pow(g, n//32, p)
    values = cubic(p, omega*omega % p)
    raw = [values(pow(omega,j,p))[1:] for j in range(32)]
    ratios = [v*pow(h,-1,p) % p if h else None for h,v in raw]
    require({i for i,c in enumerate(ratios) if c is None} == {0,2,16} and
            {i for i,c in enumerate(ratios) if c == 0} == {4,18,20} and
            {i for i,c in enumerate(ratios) if c == 1} == {6,10,14}, "pair fibers")
    u, v = g, pow(g,3,p)
    cu, cv = ratios[1], ratios[3]
    require(u != v and (u+v) % p != 0 and cu != cv and
            not {cu, cv} & {None, 0, 1}, "transverse interpolant")
    d = (cv-cu)*pow(v-u,-1,p) % p
    b = (cu-d*u) % p
    maps = [(-1,0,0,1)]
    used = [0,1]+[ratios[j] for j in VARIABLE]
    require(None not in used and len(set(used)) == 15 and not {cu,cv}&set(used),
            "fifteen regular parameters")
    for c in used:
        h = (c-b)*pow(d,-1,p) % p
        maps.append(((h-u-v) % p, u*v % p, 1, -h % p))
    for a,e,c,h in maps:
        require((a*h-e*c)%p != 0 and all((a*x+e+x*(c*x+h))%p==0
                for x in (u,v)), "regular maps share the marked points")
    for lhs,rhs in combinations(maps,2):
        a,b0,c,h = lhs
        e,f,i,j = rhs
        prodmatrix = ((j*a-f*c)%p, (j*b0-f*h)%p, (e*c-i*a)%p, (e*h-i*b0)%p)
        A,B,C,D = prodmatrix
        require(A and B and C and D and (A*D-B*C)%p, "four nonzero relative matrix entries")
    return g,raw,u,v,b,d


def stepanov(n,m,params):
    a,b,c,d = params
    require(0<a<=n and 0<c and a*c<=m and a-1+n*(c-1)<PRIME and
            0<d<=PRIME and d*(a+2*(d-1))<b*a*c, "rectangular hypotheses")
    return (a-1+n*(c-1)+m*(b-1))//d


def check_small(n):
    p = PRIME
    s = n//32
    g,raw,u,v,b,d = quotient(n)
    tags = {j+32*i:tag for j,lo,hi,tag in allocate(n) for i in range(lo,hi)}
    xs = [pow(g,i,p) for i in range(n)]
    roots = [x for i,x in enumerate(xs) if tags[i]=="root"]
    cores = [set() for _ in range(4)]
    labels = {}
    scheduled = skipped = 0
    for i,x in enumerate(xs):
        J = prod(x-z for z in roots)%p
        h,k = raw[i%32]
        L = J*h%p
        b4 = L*(b+d*x)%p
        a4 = (x*b4-d*L*(x-u)*(x-v))%p
        fs = [0,L,J*k%p]
        heads = [(x*f%p,f) for f in fs]+[(a4,b4)]
        owners = OWNERS[tags[i]]
        A,B = heads[owners[0]]
        for head in owners:
            require(heads[head]==(A,B), "defining agreement")
            cores[head].add(i)
        attempts = []
        if tags[i] not in ("d","root"):
            other = next(t for t in range(3) if heads[t]!=(A,B))
            attempts.append(other)
        if tags[i] in ("a","b","c","02","12"):
            attempts.append(3)
        if tags[i]=="d":
            attempts.extend((0,1,2))
        for head in attempts:
            scheduled += 1
            Ah,Bh = heads[head]
            if B==Bh:
                skipped += 1
                continue
            z = (Ah-A)*pow(B-Bh,-1,p)%p
            require((A+z*B-Ah-z*Bh)%p==0, "fresh agreement")
            labels[z] = (head,i)
    core = 47*s//4-1
    require(scheduled==2*n+11*s//4+1 and skipped<=15, "literal schedules")
    require(all(len(cl)==core>=n//8 for cl in cores), "interpolation uniqueness")
    require(all(i not in cores[h] for h,i in labels.values()), "outside defining cores")
    require(len(labels)>2*n, "actual scalar budget in the small model")
    print(f"n={n}: {len(labels)} bad labels at {n-core-1} errors")


def main():
    n=PRODUCTION
    allocate(n)
    quotient(n)
    s=n//32
    budget=PRIME//2**128
    hh=stepanov(n,n,(1322342,1621,812,659139))
    hs=stepanov(n,s,(419430,5101,80,205908))
    ss=stepanov(s,s,(131072,509,256,65279))
    require((hh,hs,ss)==(3960117,1243048,392196), "three collision bounds")
    loss=3*hh+39*hs+78*ss
    total=2*n+11*s//4+1
    mass=total-15-loss
    require(mass==2148807811>budget==2147483648 and n-47*s//4==679477248,
            "strict production failure")
    for small in (128,256,512):
        check_small(small)
    print(f"n={n}: {total} incidences, at most 15 poles and {loss} collisions; "
          f"at least {mass} bad labels at 679477248 errors, {mass-budget} over budget")


if __name__=="__main__":
    main()
