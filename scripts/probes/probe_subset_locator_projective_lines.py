#!/usr/bin/env python3
"""Exact line sections of three-anchor subset-locator points."""

import argparse
import itertools
import random
from collections import defaultdict


def normalize(v, p):
    for x in v:
        if x % p:
            z = pow(x % p, p - 2, p)
            return tuple(y * z % p for y in v)
    raise ValueError("zero vector")


def locator_point(subset, anchors, p):
    values = []
    for a in anchors:
        value = 1
        for x in subset:
            value = value * (a - x) % p
        values.append(value)
    return normalize(values, p)


def cross(x, y, p):
    return normalize((
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0]), p)


def census(p, domain, anchors_i, petal_i, block_size):
    anchors = [domain[i] for i in anchors_i]
    point_blocks = defaultdict(list)
    for subset_i in itertools.combinations(petal_i, block_size):
        point = locator_point([domain[i] for i in subset_i], anchors, p)
        point_blocks[point].append(subset_i)
    points = list(point_blocks)
    lines = defaultdict(set)
    for i, x in enumerate(points):
        for j in range(i + 1, len(points)):
            line = cross(x, points[j], p)
            lines[line].update((i, j))
    best_line, ids = max(lines.items(), key=lambda item: len(item[1]))
    multiplicity = max(map(len, point_blocks.values()))
    return len(points), multiplicity, len(ids), best_line, [points[i] for i in ids]


def run(p, n, generator, trials, seed):
    zeta = pow(generator, (p - 1) // n, p)
    domain = [pow(zeta, i, p) for i in range(n)]
    k = n // 4
    petal_size = 2 * k - 3
    rng = random.Random(seed)
    best = None
    for trial in range(trials):
        indices = list(range(n))
        rng.shuffle(indices)
        anchors_i = indices[:3]
        petal_i = indices[3 : 3 + petal_size]
        result = census(p, domain, anchors_i, petal_i, k - 1)
        record = (result[2], anchors_i, petal_i, result)
        if best is None or record[0] > best[0]:
            best = record
            print(
                f"trial={trial} best_line={record[0]} distinct_points={result[0]} "
                f"max_point_multiplicity={result[1]} n={n} k={k} target4k={4*k} "
                f"anchors={anchors_i} petal={petal_i} line={result[3]}"
            )
    print(f"final_best_line={best[0]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("p", type=int)
    parser.add_argument("n", type=int)
    parser.add_argument("generator", type=int)
    parser.add_argument("--trials", type=int, default=10)
    parser.add_argument("--seed", type=int, default=399)
    args = parser.parse_args()
    run(args.p, args.n, args.generator, args.trials, args.seed)
