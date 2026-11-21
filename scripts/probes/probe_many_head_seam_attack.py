#!/usr/bin/env python3
"""Check projective directions, literal folded witnesses, and the P2 inequalities."""

from math import prod
from random import Random

from probe_many_head_locator_attack import at_point, ceiling, require


def verify(n, k, heads, p):
    e = ceiling((heads - 1) * (n - k), heads)
    t = n - e
    require(t - 1 >= k, "insufficient defining sites")
    rng = Random(17 * k + heads)
    domain = rng.sample(range(p), n)
    common = domain[:k - heads]
    seam = domain[k - heads:k]
    r = t - k
    blocks = [domain[k + i*r:k + (i+1)*r] for i in range(heads)]
    extra = domain[k + heads*r:]
    width = heads + len(extra)

    def word(i, x):
        scalar = prod(x - a for a in common + seam[:i] + seam[i + 1:]) % p
        return [scalar if j == i else 0 for j in range(width)]

    word_at = {x: [0] * width for x in common + seam}
    for i, block in enumerate(blocks):
        word_at.update({x: word(i, x) for x in block})
    for j, x in enumerate(extra):
        word_at[x] = [int(i == heads + j) for i in range(width)]
    witnesses = []
    directions = set()
    for i in range(heads):
        base = common + seam[:i] + seam[i + 1:] + blocks[i]
        require(len(base) == t - 1, "incorrect defining core")
        for x in set(domain).difference(base):
            direction = [(a - b) % p for a, b in zip(word(i,x), word_at[x])]
            scale = next(value for value in direction if value)
            key = tuple(value * pow(scale, -1, p) % p for value in direction)
            require(key not in directions, "coincident projective directions")
            directions.add(key)
            witnesses.append((i, base, x, direction))
    require(len(directions) == heads * (e + 1), "direction count")

    def dot(a, b):
        return sum(x*y for x, y in zip(a, b)) % p

    for _ in range(1000):
        a, b = ([rng.randrange(p) for _ in range(width)] for _ in range(2))
        if any(dot(b, d) == 0 for _, _, _, d in witnesses):
            continue
        labels = [-dot(a, d)*pow(dot(b, d), -1, p) % p for _, _, _, d in witnesses]
        if len(set(labels)) == len(witnesses):
            break
    else:
        raise ArithmeticError("no separating pair")
    for z, (i, base, x, _) in zip(labels, witnesses):
        for y in base + [x]:
            require((dot(a, word(i,y)) + z*dot(b, word(i,y)) -
                     dot(a, word_at[y]) - z*dot(b, word_at[y])) % p == 0, "fold misses")
        explained = at_point(base[:k], [dot(b, word_at[y]) for y in base[:k]], x, p)
        require(explained != dot(b, word_at[x]), "second row has a joint fit")
    virtual = next(v for v in range(p) if v not in domain)
    chart = set()
    for i, _, x, _ in witnesses:
        a_i = seam[i]
        if x == a_i:
            received = (0, 0, 0)
            c = virtual
        else:
            c = next((seam[j] for j, block in enumerate(blocks) if x in block), virtual)
            nodal = prod(x - y for y in common + seam) % p
            w = nodal * pow(x-c, -1, p) % p
            received = (c*w % p, c*c*w % p, w)
        qi = word(i,x)[i]
        direction = (qi - received[2]) % p
        expected = (-x % p, (a_i*c - (a_i+c)*x) % p)
        actual = tuple((u-head)*pow(direction,-1,p) % p
                       for u,head in zip(received[:2], (a_i*qi, a_i*a_i*qi)))
        require(actual == expected and actual not in chart, "explicit pencil chart")
        chart.add(actual)
    print(f"n={n}, k={k}, heads={heads}, e={e}, literal labels={len(witnesses)}")


def main():
    for params in ((24,8,4,65537), (32,16,5,65537), (19,6,3,65537)):
        verify(*params)
    n = 2**30
    prime = 730750818665451459101842416358141509841924915201
    require(prime // 2**128 == 2*n, "production budget")
    for den, m, expected in ((2,5,429496730), (4,4,603979776), (8,4,704643072)):
        k = n // den
        e = ceiling((m-1)*(n-k),m)
        r = n-e-k
        require(e == expected and 0 <= r and k <= n-e-1, "production radius")
        require(k+m*r <= n < k+m*(r+1), "production packing")
        require(prime > m*m*n*n and m*(e+1) > 2*n, "production budget violation")
        print(f"n={n}, k={k}, heads={m}, e={e}, bad labels={m*(e+1)}, extra={n-k-m*r}")
        if m == 4:
            pred = e-1
            t = n-pred
            require(4*t == n+3*k+4, "predecessor deficit")
            require(3*(pred+1)+7 < 2*n and 3*pred+4 < 2*n, "four-head barrier")
            print(f"four exceptional heads at e={pred}: at most {3*(pred+1)+7} labels")
            endpoint = {4:536870911, 8:671088639}[den]
            minimum_labels = 2*n+1-3*(endpoint+1)
            max_cost = endpoint//(minimum_labels-1)
            incidence = 4*(n-endpoint)-3-max_cost
            gap = incidence-n-4*(k-1)
            require(gap == {4:5, 8:1}[den] and 3*endpoint+4 <= 2*n, "arbitrary four heads")
            print(f"all four heads at e={endpoint}: overbudget core-incidence excess={gap}")


if __name__ == "__main__":
    main()
