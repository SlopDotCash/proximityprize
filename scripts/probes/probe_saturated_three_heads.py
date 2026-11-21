#!/usr/bin/env python3
"""Reconstruct the saturated three-head example and check its folded witnesses."""

from fractions import Fraction
from math import ceil, comb, prod


def inverse(matrix, p):
    rows = [row[:] + [int(i == j) for j in range(3)] for i, row in enumerate(matrix)]
    for i in range(3):
        k = next(k for k in range(i, 3) if rows[k][i] % p)
        rows[i], rows[k] = rows[k], rows[i]
        inv = pow(rows[i][i], -1, p)
        rows[i] = [x * inv % p for x in rows[i]]
        for k in range(3):
            if k != i:
                c = rows[k][i]
                rows[k] = [(x-c*y) % p for x, y in zip(rows[k], rows[i])]
    return [r[3:] for r in rows]


def project(a, b, p):
    return a * pow(b, -1, p) % p if b else None


def reproduce(n, k, p, g):
    assert pow(g, n//2, p) == p-1
    t, rem = divmod(n + 2*(k-1), 3)
    assert rem == 0 and k <= t
    t += 1
    group = [pow(g, i, p) for i in range(n)]
    roots = group[::n//8][:6]
    pairs = list(zip(roots[::2], roots[1::2]))
    matrix = [[a*b % p for a, b in pairs], [(-a-b) % p for a, b in pairs], [1, 1, 1]]
    dual = inverse(matrix, p)
    def direction(i, x):
        u, v, w = dual[i]
        return ((u*x-v) % p, (v*x-w) % p)
    def neighbors(i):
        return [j for j in range(3) if j != i]
    directions = {}
    for x in group:
        active = neighbors(roots.index(x)//2) if x in roots else range(3)
        for j in active:
            a, b = direction(j, x)
            assert a or b
            directions.setdefault(project(b, a, p), set()).add(x)
    # Keep one site from each collision class, preferring a marked point.
    deleted = set()
    for sites in directions.values():
        marked = sites.intersection(roots)
        assert len(marked) <= 1
        retained = min(marked or sites)
        deleted.update(sites - {retained})
    required = len(deleted)
    assert required <= k-4, (n, required, k-4)
    deleted.update(x for x in [x for x in group if x not in deleted and x not in roots][:k-4-required])
    private = [x for x in group if x not in deleted and x not in roots]
    assert len(private) % 3 == 0
    owners = {x: i % 3 for i, x in enumerate(private)}
    # Rotate all row pairs so every used fresh direction has a finite label.
    all_directions = set(directions)
    shift = next(v for v in range(p) if (-v % p) not in all_directions)
    words = {j: {} for j in range(3)}
    received = {}
    for x in group:
        factor = prod((x-a) % p for a in deleted) % p
        edges = []
        for j, (a, b) in enumerate(pairs):
            v0, v1 = direction(j, x)
            c = factor*(x-a)*(x-b) % p
            edges.append((c*v0 % p, c*(v1 + shift*v0) % p))
        assert sum(v[0] for v in edges) % p == sum(v[1] for v in edges) % p == 0
        # Differences W0-W1, W1-W2, W2-W0 are the three signed edges.
        points = [(0, 0), tuple(-y % p for y in edges[0]), edges[2]]
        for j, pt in enumerate(points):
            words[j][x] = pt
        owner = owners.get(x, roots.index(x)//2 if x in roots else 0)
        received[x] = points[owner]
    labels = set()
    for j in range(3):
        core = [x for x in group if received[x] == words[j][x]]
        assert len(core) == t-1
        for x in group:
            if received[x] != words[j][x]:
                a, b = words[j][x]
                u, v = received[x]
                z = (a-u) * pow(v-b, -1, p) % p
                assert z not in labels
                labels.add(z)
                assert (a+z*b-u-z*v) % p == 0
    assert len(labels) == 3*(n-t+1)
    print(f"n={n}, k={k}, p={p}: {required} collision sites deleted, "
          f"{len(labels)} bad labels at {n-t} errors")


def predecessor_cap():
    n = 2**30
    d = n//8 - 1
    e = 626349396
    t = n - e
    small = e//128 + 1
    caps = [0, small]
    for b, cutoff in enumerate((9000000, 17000000, 25000000, 34000000, 46000000), 2):
        a, mu, J = 16, 64, max(17*b-1, 90)
        w = Fraction(814*n, 1000)
        assert a*a*(54*b-b*b)*(J+1)*((2*b+1)*w-b*b*d-b) < (cutoff+1)*n
        assert (cutoff-209)*(Fraction(mu, 12)-Fraction(27, 10)) > 210*mu*6 + 27*comb(mu+1, 2)
        caps.append(b*cutoff + 8500)
    for i in range(1, 7):
        assert all(caps[j] + caps[i-j] <= caps[i] for j in range(1, i))
    z = t-127
    assert 4*t > n+5*d+381
    values = []
    for j in range(7):
        union = max(j*z-comb(j, 2)*d, ceil(Fraction(j*z*z, z+(j-1)*d)))
        base = j*(e+1) if j < 3 else j*n-(j-1)*union
        values.append(base + caps[6-j] + 74)
    assert 3*(t-1) - (n+2*d) == 3
    # Truncate the three nonnegative core deficits at total three.
    triples = [(i, j, 3-i-j) for i in range(4) for j in range(4-i)]
    noncollinear = max(sum(1+e//(1+h) for h in v) for v in triples)
    assert max(values + [noncollinear]) == noncollinear == 1409286144
    print(f"Predecessor ceilings by head count: {values}; noncollinear: {noncollinear}")
    return noncollinear


def production_primes():
    n = 2**30
    k = n//8
    t = 1+(n+2*(k-1))//3
    e = n-t
    assert (e, t, 3*(t-1)) == (626349397, 447392427, n+2*(k-1))
    # A self-contained Stepanov certificate for the number of deletion sites.
    A, B, C, T = 32768, 128, 128, 8192
    assert A*B <= n and A*B*C > T*(A+T-1)
    collision_bound = (A-1+n*(B+C-2))//T
    assert 3*collision_bound == 99876873 < k-4
    lo, hi = predecessor_cap(), 3*(e+1)-1
    assert hi-lo+1 == 469762050
    for budget in [lo, (lo+hi)//2, hi-2, hi-1, hi]:
        for r in range(1, 10000, 2):
            odd = budget*2**48 + r
            p = odd*2**80 + 1
            witness = next((a for a in (3, 5) if pow(a, (p-1)//2, p) == p-1), None)
            if witness is not None:
                assert odd < 2**80 and p//2**128 == budget and (p-1) % n == 0
                print(f"budget={budget}, p={p}, odd={odd}, Proth witness={witness}")
                break
        else:
            raise AssertionError("no prime certificate found")


if __name__ == "__main__":
    for p, generator, cases in [(65537, 3, [(256, 32), (1024, 128)]),
                                (2013265921, 31, [(64, 8), (256, 32), (1024, 128)])]:
        for n, k in cases:
            reproduce(n, k, p, pow(generator, (p-1)//n, p))
    production_primes()
