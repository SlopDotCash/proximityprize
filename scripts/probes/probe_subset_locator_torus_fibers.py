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


def run(p, n, generator, trials, seed):
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
        result = max_fiber(
            [domain[i] for i in left_i], [domain[i] for i in right_i],
            block_size, [domain[i] for i in anchors_i], p)
        record = (result[0], anchors_i, left_i, right_i, result[1], result[2])
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
    args = parser.parse_args()
    run(args.p, args.n, args.generator, args.trials, args.seed)
