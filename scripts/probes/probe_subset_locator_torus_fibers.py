#!/usr/bin/env python3
"""Exact three-anchor locator fibers for general overlap-three petals."""

import argparse
import itertools
import random
from collections import Counter


def projective_ratio(v, u, p):
    raw = tuple(v[i] * pow(u[i], p - 2, p) % p for i in range(3))
    for x in raw:
        if x:
            z = pow(x, p - 2, p)
            return tuple(y * z % p for y in raw)
    raise ValueError("zero ratio")


def locator_value(subset, anchors, p):
    out = []
    for a in anchors:
        value = 1
        for x in subset:
            value = value * (a - x) % p
        out.append(value)
    return tuple(out)


def max_fiber(left, right, block_size, anchors, p):
    left_values = [
        (s, locator_value(s, anchors, p))
        for s in itertools.combinations(left, block_size)
    ]
    right_values = [
        (s, locator_value(s, anchors, p))
        for s in itertools.combinations(right, block_size)
    ]
    counts = Counter()
    sample = {}
    for ls, u in left_values:
        for rs, v in right_values:
            d = projective_ratio(v, u, p)
            counts[d] += 1
            if counts[d] <= 12:
                sample.setdefault(d, []).append((ls, rs))
    d, count = counts.most_common(1)[0]
    return count, d, sample[d]


def normalize(v, p):
    for x in v:
        if x % p:
            z = pow(x % p, p - 2, p)
            return tuple(y * z % p for y in v)
    raise ValueError("zero vector")


def cross(x, y, p):
    return normalize((
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0]), p)


def max_collinear_torus_fiber(left, right, block_size, anchors, p):
    left_points = {
        normalize(locator_value(s, anchors, p), p)
        for s in itertools.combinations(left, block_size)
    }
    right_points = {
        normalize(locator_value(s, anchors, p), p)
        for s in itertools.combinations(right, block_size)
    }
    fibers = {}
    for u in left_points:
        for v in right_points:
            d = projective_ratio(v, u, p)
            fibers.setdefault(d, set()).add(u)
    best = (0, None, None)
    for d, points_set in fibers.items():
        if len(points_set) <= best[0]:
            continue
        points = list(points_set)
        line_points = {}
        for i, x in enumerate(points):
            for j in range(i + 1, len(points)):
                line = cross(x, points[j], p)
                line_points.setdefault(line, set()).update((i, j))
        if line_points:
            line, ids = max(line_points.items(), key=lambda item: len(item[1]))
            if len(ids) > best[0]:
                best = (len(ids), d, line)
    return best, len(left_points), len(right_points)


def identity_intersection(left, right, block_size, anchors, p):
    left_points = {
        normalize(locator_value(s, anchors, p), p)
        for s in itertools.combinations(left, block_size)
    }
    right_points = {
        normalize(locator_value(s, anchors, p), p)
        for s in itertools.combinations(right, block_size)
    }
    common = list(left_points & right_points)
    best = 1 if common else 0
    best_line = None
    line_points = {}
    for i, x in enumerate(common):
        for j in range(i + 1, len(common)):
            line = cross(x, common[j], p)
            line_points.setdefault(line, set()).update((i, j))
    if line_points:
        best_line, ids = max(line_points.items(), key=lambda item: len(item[1]))
        best = len(ids)
    return (best, len(common), best_line), len(left_points), len(right_points)


def run(p, n, generator, trials, seed, collinear, identity):
    zeta = pow(generator, (p - 1) // n, p)
    domain = [pow(zeta, i, p) for i in range(n)]
    k = n // 4
    petal_size = 2 * k - 3
    block_size = k - 1
    rng = random.Random(seed)
    best = None
    for trial in range(trials):
        indices = list(range(n))
        rng.shuffle(indices)
        anchors_i = indices[:3]
        left_i = indices[3 : 3 + petal_size]
        right_i = indices[3 + petal_size : 3 + 2 * petal_size]
        if len(right_i) < petal_size:
            raise ValueError("domain too short for disjoint petals")
        solver = identity_intersection if identity else (
            max_collinear_torus_fiber if collinear else max_fiber)
        result = solver([domain[i] for i in left_i], [domain[i] for i in right_i],
            block_size, [domain[i] for i in anchors_i], p)
        if collinear or identity:
            score = result[0][0]
            parameter = result[0][1:]
            sample = (result[1], result[2])
        else:
            score = result[0]
            parameter = result[1]
            sample = result[2]
        record = (score, anchors_i, left_i, right_i, parameter, sample)
        if best is None or record[0] > best[0]:
            best = record
            print(
                f"trial={trial} best={best[0]} n={n} k={k} target4k={4*k} "
                f"anchors={anchors_i} left={left_i} right={right_i} d={best[4]}"
            )
    print(f"final_best={best[0]} sample={best[5]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("p", type=int)
    parser.add_argument("n", type=int)
    parser.add_argument("generator", type=int)
    parser.add_argument("--trials", type=int, default=20)
    parser.add_argument("--seed", type=int, default=398)
    parser.add_argument("--collinear", action="store_true")
    parser.add_argument("--identity", action="store_true")
    args = parser.parse_args()
    run(args.p, args.n, args.generator, args.trials, args.seed,
        args.collinear, args.identity)
