#!/usr/bin/env python3
"""Exact first-prime trace-quotient search on mu_64.

Each endpoint has seven trace roots, forming at most two intervals in some
angular ordering. The two endpoint orderings can be chosen independently.
"""
from collections import defaultdict
from itertools import combinations
from math import prod

PRIME = 2**158 + 192 * 2**30 + 1
OMEGA = 321066668146402433440778728016715546214271526818
ROOTS = [pow(OMEGA, i, PRIME) for i in range(64)]


def angular_masks(reflection, representatives):
    index = {v: i for i, v in enumerate(representatives)}
    masks = set()
    size = len(index)
    for left_size in range(1, 8):
        right_size = 7 - left_size
        for i in range(size - left_size + 1):
            for j in range(i + left_size, size - right_size + 1):
                support = representatives[i:i + left_size] + representatives[j:j + right_size]
                for t in range(1, 64, 2):
                    for shift in (0, 32):
                        offset = reflection * (1 - t) // 2 + shift
                        exponents = [(t * v + offset) % 64 for v in support]
                        mask = sum(1 << index[min(v, (reflection - v) % 64)] for v in exponents)
                        assert mask.bit_count() == 7
                        masks.add(mask)
    return sorted(masks)


def census(reflection):
    representatives = sorted({min(i, (reflection - i) % 64) for i in range(64)})
    points = [(ROOTS[i] + ROOTS[(reflection - i) % 64]) % PRIME for i in representatives]
    weight = [1 + int((2 * i - reflection) % 64 != 0) for i in representatives]
    assert len(set(points)) == len(points) and sum(weight) == 64
    masks = angular_masks(reflection, representatives)
    size = len(masks)
    rows = range(len(points))
    differences = [[(x - y) % PRIME for y in points] for x in points]
    inverses = [[pow(x, -1, PRIME) if x else 0 for x in row] for row in differences]
    values, inverse_values = [[] for _ in rows], [[] for _ in rows]
    weights = []
    containers = [bytearray((size + 7) // 8) for _ in rows]
    for index, mask in enumerate(masks):
        support = [i for i in rows if mask >> i & 1]
        weights.append(sum(weight[i] for i in support))
        for i in support:
            containers[i][index // 8] |= 1 << (index % 8)
        for i in rows:
            values[i].append(prod(differences[i][j] for j in support) % PRIME)
            inverse_values[i].append(prod(inverses[i][j] for j in support) % PRIME)
    containers = [int.from_bytes(x, 'little') for x in containers]
    directed = 0
    for mask in masks:
        forbidden = 0
        for node in rows:
            if mask >> node & 1:
                forbidden |= containers[node]
        directed += size - forbidden.bit_count()

    # Without a collision at two trace nodes, the third fiber contributes
    # at most two original sites. This bound is attained on disjoint intervals.
    a0 = sum(1 << i for i in range(1, 8))
    b0 = sum(1 << i for i in range(8, 15))
    assert a0 in masks and b0 in masks and all(weight[i] == 2 for i in range(1, 16))
    best = 18
    tested = set()
    for i, j in combinations(rows, 2):
        buckets = defaultdict(list)
        for h, (u, v) in enumerate(zip(values[i], inverse_values[j])):
            if u and v:
                buckets[u * v % PRIME].append(h)
        for group in buckets.values():
            for a, b in combinations(group, 2):
                if masks[a] & masks[b] or (a, b) in tested:
                    continue
                tested.add((a, b))
                masses = defaultdict(int)
                for k in rows:
                    u, v = values[k][a], inverse_values[k][b]
                    if u and v:
                        masses[u * v % PRIME] += weight[k]
                best = max(best, 2 * (weights[a] + weights[b] + max(masses.values())) - 42)
    return size, directed // 2, len(tested), best


if __name__ == '__main__':
    assert pow(OMEGA, 32, PRIME) == PRIME - 1
    for a, expected in enumerate([(32504, 0, 18), (31040, 128, 22)]):
        sets, pairs, collisions, score = census(a)
        print(f'reflection={a} endpoint_sets={sets} disjoint_pairs={pairs} '
              f'pairs_with_repeated_ratio={collisions} maximum_score={score}', flush=True)
        assert (sets, collisions, score) == expected
