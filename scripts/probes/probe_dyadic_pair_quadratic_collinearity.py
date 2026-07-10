#!/usr/bin/env python3
"""Census lines through quadratic coefficient points of dyadic-domain pairs."""

import argparse
import itertools
from collections import defaultdict


def inv(a: int, p: int) -> int:
    return pow(a % p, p - 2, p)


def normalize_line(a: int, b: int, c: int, p: int):
    values = (a % p, b % p, c % p)
    for value in values:
        if value:
            scale = inv(value, p)
            return tuple(x * scale % p for x in values)
    raise ValueError("zero line")


def run(p: int, n: int, generator: int) -> None:
    zeta = pow(generator, (p - 1) // n, p)
    domain = [pow(zeta, i, p) for i in range(n)]
    pairs = list(itertools.combinations(range(n), 2))
    points = [(1, -(domain[i] + domain[j]) % p, domain[i] * domain[j] % p)
              for i, j in pairs]
    lines = defaultdict(set)
    for a in range(len(pairs)):
        x = points[a]
        for b in range(a + 1, len(pairs)):
            y = points[b]
            line = normalize_line(
                x[1] * y[2] - x[2] * y[1],
                x[2] * y[0] - x[0] * y[2],
                x[0] * y[1] - x[1] * y[0], p)
            lines[line].update((a, b))
    histogram = defaultdict(int)
    max_nonstar = 0
    witness = None
    for ids in lines.values():
        histogram[len(ids)] += 1
        common = set(pairs[next(iter(ids))])
        for idx in ids:
            common &= set(pairs[idx])
        if not common and len(ids) > max_nonstar:
            max_nonstar = len(ids)
            witness = [pairs[idx] for idx in sorted(ids)]
    print(f"p={p} n={n} zeta={zeta} histogram={dict(sorted(histogram.items()))}")
    print(f"max_nonstar={max_nonstar} witness={witness}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("p", type=int)
    parser.add_argument("n", type=int)
    parser.add_argument("generator", type=int)
    args = parser.parse_args()
    run(args.p, args.n, args.generator)
