#!/usr/bin/env python3
"""Verify the target-independent compression bound and compressed constant cases."""
from itertools import combinations_with_replacement, product
from math import gcd


def pairing(c, a, i, j, k, l, prime):
    out = {}
    for u, su in ((i, 1), (j, -1)):
        for v, sv in ((k, 1), (l, -1)):
            e = a[u]+a[v]
            out[e] = (out.get(e, 0) + c[u]*c[v]*su*sv) % prime
    return out


def constant_cases():
    prime = 257
    k = [1, 2, prime-1, prime-2]
    tested = harmonic = 0
    for a in combinations_with_replacement(range(5), 4):
        if len(set(a)) == 1:
            continue
        for c in product(k, repeat=4):
            if len(set(zip(a, c))) != 4:
                continue
            p = pairing(c, a, 0, 1, 2, 3, prime)
            q = pairing(c, a, 0, 2, 1, 3, prime)
            ex = next(i for i in q if q[i])
            constant = all((p.get(i, 0)*q[ex]-q.get(i, 0)*p.get(ex, 0)) % prime == 0
                           for i in set(p) | set(q))
            expected = (a[0] < a[1] == a[2] < a[3] and a[0]+a[3] == 2*a[1]
                        and (c[1]+c[2]) % prime == 0
                        and (c[0]*c[3]-c[1]*c[1]) % prime == 0)
            assert constant == expected
            tested += 1
            harmonic += constant
    print("compressed constant test", tested, "harmonic tuples", harmonic)


def compression(a, n, k):
    forms = [a[0]+a[1]-a[2]-a[3], a[0]-a[1]+a[2]-a[3], a[0]-a[1]-a[2]+a[3]]
    seen = {}
    for i in range(k**3+1):
        point = tuple(i*f % n for f in forms)
        box = tuple(v*k//n for v in point)
        if box in seen:
            j, prev = seen[box]
            vals = [v-w for v, w in zip(point, prev)]
            break
        seen[box] = i, point
    else:
        raise AssertionError("Dirichlet box count")
    h = i-j
    signs = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
    eps = vals[0] % 2
    b = [(sum(u*v for u, v in zip(row, vals))-eps)//2 for row in signs]
    assert all((x-b[0]-2*h*(y-a[0])) % n == 0 for x, y in zip(b, a))
    assert len(set(b)) >= 2
    exps = [b[u]+b[v] for u in range(4) for v in range(u)]
    assert k*(max(exps)-min(exps)) < 2*n
    return h, gcd(n, 2*h), max(exps)-min(exps)


def named_scales():
    k = 49
    for level in range(18, 31):
        n = 2**level
        assert 2*k**3 < n
        # 16*[C + (n-C)*6/k] < 9n at C=n/2+4.
        c = n//2+4
        assert 16*(k*c+6*(n-c)) < 9*n*k
    for a, n in [((0, 17, 512, 615), 2**18),
                 ((0, 2**25, 2**27+11, 2**26+19), 2**30)]:
        h, g, span = compression(a, n, k)
        print("compression", n, "step", h, "cosets", g, "width", span)


if __name__ == "__main__":
    constant_cases()
    named_scales()
