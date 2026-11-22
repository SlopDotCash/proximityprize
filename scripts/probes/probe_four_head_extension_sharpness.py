#!/usr/bin/env python3
"""Reconstruct all four personal capacities over the second named prime at k=4."""

from itertools import combinations, count
from math import prod

from probe_quarter_slope_reconstruction import MAPS, P, double_sites, interpolate


def heads(x):
    edges = {}
    for j, (a, b, c, d) in enumerate(MAPS, 1):
        num, den = a*x + b, c*x + d
        opposite = tuple(i for i in range(1, 4) if i != j)
        edges[0, j] = (den + num) % P
        edges[opposite] = (den - num) % P
    return tuple((prod(v for edge, v in edges.items() if i in edge) % P,
                  prod(v for edge, v in edges.items() if i not in edge) % P)
                 for i in range(4))


def labels_at(values, owners):
    u, v = values[owners[0]]
    assert tuple(i for i in range(4) if values[i] == (u, v)) == owners
    return {i: (u-a) * pow(b-v, -1, P) % P for i, (a, b) in enumerate(values)
            if i not in owners}


def verify(singletons):
    site = {}
    used = set()

    def add(x, owners):
        labels = labels_at(heads(x), owners)
        assert x not in site and len(set(labels.values())) == len(labels)
        assert used.isdisjoint(labels.values())
        site[x] = owners
        used.update(labels.values())

    for j, k in combinations(range(3), 2):
        for sign, owners in ((1, (0, 4-j-k)), (-1, (j+1, k+1))):
            for x in double_sites(j, k, sign):
                add(x, owners)
    candidates = count(1)
    for i in range(4):
        for _ in range(singletons):
            for x in candidates:
                values = heads(x)
                if x in site or len(set(values)) != 4 or len({v for _, v in values}) != 4:
                    continue
                fresh = set(labels_at(values, (i,)).values())
                if len(fresh) == 3 and used.isdisjoint(fresh):
                    add(x, (i,))
                    break
    n, t = 12 + 4*singletons, 7 + singletons
    assert len(site) == n and len(used) == 4*(n-t+1)
    word = {x: heads(x)[owners[0]] for x, owners in site.items()}
    for i in range(4):
        core = [x for x in site if i in site[x]]
        assert len(core) == t-1
        base = core[:4]
        for x in site.keys()-set(core):
            gamma = labels_at(heads(x), site[x])[i]
            folded = [(word[y][0] + gamma*word[y][1]) % P for y in base]
            for y in core + [x]:
                assert interpolate(base, folded, y) == (word[y][0]+gamma*word[y][1]) % P
            predicted = tuple(interpolate(base, [word[y][r] for y in base], x) for r in range(2))
            assert predicted == heads(x)[i] and predicted != word[x]
    print(f'n={n}, k=4, e={n-t}, {len(used)} distinct literal MCA-bad scalar labels')


if __name__ == '__main__':
    verify(1)
    verify(5)
