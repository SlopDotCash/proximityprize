#!/usr/bin/env python3
"""Verify the second production prime's noncollinear cubic quartet and four defining cores."""

from itertools import combinations
from math import prod

from probe_smooth_four_head_attack import PRIME, GENERATOR
from probe_many_head_locator_attack import require


def quartet(prime, root):
    """Return the four planar cubics on a sixteenth root of unity, by interpolation."""
    xs = [pow(root, j, prime) for j in range(16)]

    def locator(js, t):
        return prod(t-xs[j] for j in js) % prime

    def ratio(a, b):
        return a * pow(b, -1, prime) % prime

    def first(t):
        return locator([0, 2, 4], t), 0

    scalar = ratio(first(xs[6])[0], locator([5, 13], xs[6]))

    def second(t):
        v = locator([5, 13], t)
        return scalar*v % prime, v*(t-xs[6]) % prime

    nodes = (8, 10, 12, 15)
    values = [second(xs[j]) for j in nodes[:3]] + [first(xs[15])]

    def fourth(t):
        weights = [ratio(locator([j for j in nodes if j != i], t),
                         locator([j for j in nodes if j != i], xs[i])) for i in nodes]
        return tuple(sum(a*v[k] for a, v in zip(weights, values)) % prime for k in range(2))

    # The second-row projection U+V separates distinct heads at every quotient site.
    def evaluate(t):
        return [(u, (u+v) % prime) for u, v in ((0, 0), first(t), second(t), fourth(t))]

    return [evaluate(t) for t in xs]


PAIRS = {(0, 1): (0, 2, 4), (0, 2): (5, 13), (0, 3): (14,),
         (1, 2): (6,), (1, 3): (7, 15), (2, 3): (8, 10, 12)}
PRIVATE = (1, 3, 9, 11)


def main():
    scale = 2**26
    n, k = 16*scale, 4*scale
    root = pow(GENERATOR, scale, PRIME)
    require(pow(root, 8, PRIME) == PRIME-1, "sixteenth root")
    words = quartet(PRIME, root)
    for pair, sites in PAIRS.items():
        a, b = pair
        require(tuple(j for j, vals in enumerate(words) if vals[a] == vals[b]) == sites,
                "pair coincidences")
        require(tuple(j for j, vals in enumerate(words) if vals[a][1] == vals[b][1]) == sites,
                "second-row coincidences")
    for j, vals in enumerate(words):
        for a, b, c in combinations(range(4), 3):
            distinct = len({vals[a], vals[b], vals[c]}) == 3
            u, v, w = vals[a], vals[b], vals[c]
            det = ((v[0]-u[0])*(w[1]-u[1])-(v[1]-u[1])*(w[0]-u[0])) % PRIME
            require(bool(det) == distinct, "separation of foreign slopes")
    common = scale-2
    core = []
    for i in range(4):
        pair_sites = sum(len(z) for p, z in PAIRS.items() if i in p)*scale
        private = 3*scale//4 + int(i < 2)
        core.append(common + pair_sites + private)
    e = n-min(core)-1
    labels = 12*scale*2 + (3*scale+2)*3
    require(common+3*scale+1 < k <= min(core), "degree and core bounds")
    require((e, labels) == (553648129, 2214592518), "production endpoint")
    require(PRIME//2**128 < labels and labels*(labels-1)//2 < PRIME, "field budgets")
    print(f"{e} errors, {labels} bad labels, {core} defining sites")


if __name__ == "__main__":
    main()
