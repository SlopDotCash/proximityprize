#!/usr/bin/env python3
"""Exhaustive fibers of A(x)=r1(x)/H(x) for [16,4] support triples over F17."""

import itertools
from collections import Counter


P = 17
DOMAIN = [pow(3, i, P) for i in range(16)]


def eval_poly(c, x):
    return sum(c[i] * pow(x, i, P) for i in range(len(c))) % P


def run():
    best = None
    histogram = Counter()
    for support in itertools.combinations(range(16), 3):
        support_values = [DOMAIN[i] for i in support]
        zero = [i for i in range(16) if i not in support]
        hvals = []
        for i in zero:
            value = 1
            for y in support_values:
                value = value * (DOMAIN[i] - y) % P
            hvals.append(value)
        for coeffs in itertools.product(range(P), repeat=3):
            if coeffs == (0, 0, 0):
                continue
            # Exact support requires the interpolated direction to be nonzero
            # at all three support coordinates.
            if any(eval_poly(coeffs, x) == 0 for x in support_values):
                continue
            fibers = Counter(
                eval_poly(coeffs, DOMAIN[i]) * pow(hvals[j], P - 2, P) % P
                for j, i in enumerate(zero)
            )
            profile = tuple(sorted(fibers.values(), reverse=True))
            histogram[profile] += 1
            triple_classes = sum(size == 3 for size in fibers.values())
            score = (triple_classes, profile)
            if best is None or score > best[0]:
                best = (score, support, coeffs, dict(fibers))
                print(
                    f"best_triple_classes={triple_classes} profile={profile} "
                    f"support={support} coeffs={coeffs} fibers={dict(fibers)}"
                )
    print(f"final_best={best}")
    print(f"profiles={len(histogram)}")


if __name__ == "__main__":
    run()
