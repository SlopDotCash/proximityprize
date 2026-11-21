#!/usr/bin/env python3
"""Reconstruct all the fresh witnesses for three heads with three pairwise intersections."""

from fractions import Fraction as Q
from math import comb, prod

from probe_second_prime_intrinsic_quartic import require


def check_small(k, p):
    n = 16*k
    xs = [(x*x + 13*x + 7) % p for x in range(n)]
    require(len(set(xs)) == n and p > 3*n*n, "injective domain and field size")
    common = set(xs[:k-3])
    a, b, g = xs[k-3:k]
    cores = [common | {a,b}, common | {a,g}, common | {b,g}]
    for i in range(3):
        cores[i].update(xs[k+i*5*k:k+(i+1)*5*k])
    require(all(len(C) == 6*k-1 for C in cores), "pinned heads")
    inv_a, inv_b = pow(g-a, -1, p), pow(g-b, -1, p)

    def head(x, i, s):
        h = prod(x-y for y in common) % p
        if i == 0:
            return (0, 0)
        seam, slope, inv = (a,s,inv_a) if i == 1 else (b,1,inv_b)
        return (h*(x-seam)*slope*(x-g) % p, h*(x-seam)*inv % p)

    def owner(x):
        return next(i for i in range(3) if x in cores[i])

    # Use evaluations at two choices of s to recover each affine scalar function.
    slots = [(i,x) for i in range(3) for x in xs if x not in cores[i]]
    functions = {}
    for i,x in slots:
        values = []
        for s in (0,1):
            u,v = head(x,owner(x),s)
            c,d = head(x,i,s)
            require(v != d, "fresh row differs")
            values.append((c-u) * pow(v-d,-1,p) % p)
        functions[i,x] = ((values[1]-values[0]) % p, values[0])
    require(len(set(functions.values())) == 30*k+3, "projective separation")
    forbidden = set()
    lines = list(functions.values())
    for idx,(v,w) in enumerate(lines):
        for vv,ww in lines[:idx]:
            if v != vv:
                forbidden.add((ww-w)*pow(v-vv,-1,p) % p)
    s = next(s for s in range(p) if s not in forbidden)
    rows = {x:head(x,owner(x),s) for x in xs}
    labels = set()
    for (i,x), (v,w) in functions.items():
        z = (v*s+w) % p
        require(z not in labels, "distinct actual scalar")
        labels.add(z)
        require(all(head(y,i,s)==rows[y] for y in cores[i]), "joint agreement on core")
        require(rows[x] != head(x,i,s) and len(cores[i]) >= k, "joint extension fails")
        for y in cores[i] | {x}:
            u0,u1 = rows[y]
            a0,a1 = head(y,i,s)
            require((u0+z*u1-a0-z*a1) % p == 0, "fold agrees")
    return len(labels)


def main():
    k = 2**26
    n,e = 16*k,10*k-1
    B = 2*(e+1)+1+e//3
    require(B==1565873494 and 30*k+2==2013265922, "budget plateau")
    require(15*n//8+3==30*k+3 and 3*n*n>comb(30*k+3,2), "next interval")
    require(3*(6*k)-n-2*(k-1)==2, "forced total deficits")
    require(50*(6*k+1)-70*(k-1)-14*n==6*k+120, "cubic relation")
    require(B+1-13>5*n//4-34, "cubic population")
    require(6*k+1-e//512>Q(373,1000)*n, "core fraction")
    require(3*n-2*(3*Q(373,1000)*n-3*(k-1))+13 < B, "collinear capacity")
    for dim, prime in ((3,65537),(4,65537),(8,131071)):
        print(f"n={16*dim} k={dim} e={10*dim} verified_bad_labels={check_small(dim,prime)}")
    print(f"n={n} plateau={B}..{30*k+2} first_bad={10*k}")


if __name__ == "__main__":
    main()
