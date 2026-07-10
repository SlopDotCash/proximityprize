#!/usr/bin/env python3
"""Exact diagonal-projectivity fibers for complementary pair locators."""

import argparse
import itertools
import random
from collections import Counter


def projective(v, p):
    for x in v:
        if x % p:
            z = pow(x % p, p - 2, p)
            return tuple(y * z % p for y in v)
    raise ValueError("zero projective vector")


def pair_value(x, y, anchors, p):
    return tuple((a - x) * (a - y) % p for a in anchors)


def max_fiber(left, right, anchors, p):
    lp = [(e, pair_value(*e, anchors, p)) for e in itertools.combinations(left, 2)]
    rp = [(e, pair_value(*e, anchors, p)) for e in itertools.combinations(right, 2)]
    counts = Counter()
    witnesses = {}
    for le, u in lp:
        for re, v in rp:
            # Diagonal d sends u projectively to v. Anchors are disjoint from petals,
            # so all coordinates are nonzero; normalize d0=1.
            d = projective(tuple(v[i] * pow(u[i], p - 2, p) % p for i in range(3)), p)
            counts[d] += 1
            witnesses.setdefault(d, []).append((le, re))
    d, count = counts.most_common(1)[0]
    return count, d, witnesses[d]


def run(p, n, generator, trials, seed):
    zeta = pow(generator, (p - 1) // n, p)
    domain = [pow(zeta, i, p) for i in range(n)]
    rng = random.Random(seed)
    k = n // 4
    best = None
    for trial in range(trials):
        indices = list(range(n))
        rng.shuffle(indices)
        anchors_i = indices[:3]
        left_i = indices[3 : 3 + k + 1]
        right_i = indices[3 + k + 1 : 3 + 2 * (k + 1)]
        if len(right_i) < k + 1:
            raise ValueError("domain too short for disjoint test sets")
        result = max_fiber(
            [domain[i] for i in left_i], [domain[i] for i in right_i],
            [domain[i] for i in anchors_i], p)
        record = (result[0], anchors_i, left_i, right_i, result[1], result[2])
        if best is None or record[0] > best[0]:
            best = record
            print(
                f"trial={trial} best={best[0]} n={n} k={k} target4k={4*k} "
                f"anchors={anchors_i} left={left_i} right={right_i} d={best[4]}"
            )
    print(f"final_best={best[0]} witness={best[5]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("p", type=int)
    parser.add_argument("n", type=int)
    parser.add_argument("generator", type=int)
    parser.add_argument("--trials", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=397)
    args = parser.parse_args()
    run(args.p, args.n, args.generator, args.trials, args.seed)
