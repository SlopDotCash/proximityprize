#!/usr/bin/env python3
"""Exhaust small MDS syndrome spaces for the proposed 2e+1 line bound."""

from itertools import combinations, product


def inv(a, p):
    return pow(a, p - 2, p)


def normalize(v, p):
    for x in v:
        if x:
            z = inv(x, p)
            return tuple((z * y) % p for y in v)
    raise ValueError("zero vector")


def span(columns, p, dimension):
    values = set()
    for coeffs in product(range(p), repeat=len(columns)):
        values.add(tuple(sum(a * col[j] for a, col in zip(coeffs, columns)) % p
                         for j in range(dimension)))
    return values


def representation(target, columns, support, p):
    for coeffs in product(range(p), repeat=len(support)):
        if all(sum(a * columns[i][j] for a, i in zip(coeffs, support)) % p == target[j]
               for j in range(len(target))):
            return coeffs
    return None


def audit(n, k, e, p):
    d = n - k
    points = list(range(1, n + 1))
    columns = [tuple(pow(x, j, p) for j in range(d)) for x in points]
    support_spaces = [span([columns[i] for i in support], p, d)
                      for support in combinations(range(n), e)]
    ball = set().union(*support_spaces)
    vectors = list(product(range(p), repeat=d))
    directions = sorted({normalize(v, p) for v in vectors if any(v)})

    best = (-1, None)
    histogram = {}
    for direction in directions:
        # Quotient affine bases by translations along the direction: first zeroable
        # coordinate is fixed to zero, yielding one representative per affine line.
        pivot = next(i for i, x in enumerate(direction) if x)
        for base in vectors:
            if base[pivot] != 0:
                continue
            hits = []
            for gamma in range(p):
                point = tuple((base[j] + gamma * direction[j]) % p for j in range(d))
                if point in ball:
                    hits.append(gamma)
            joint = any(base in space and direction in space for space in support_spaces)
            if joint:
                continue
            histogram[len(hits)] = histogram.get(len(hits), 0) + 1
            if len(hits) > best[0]:
                best = (len(hits), (base, direction, hits))

    print({"n": n, "k": k, "e": e, "p": p, "D": d,
           "ball": len(ball), "lines": sum(histogram.values()),
           "bound": 2 * e + 1, "best": best, "histogram": histogram})
    if best[0] >= n and best[1] is not None:
        base, direction, hits = best[1]
        for gamma in hits:
            target = tuple((base[j] + gamma * direction[j]) % p for j in range(d))
            reps = []
            for support in combinations(range(n), e):
                coeffs = representation(target, columns, support, p)
                if coeffs is not None:
                    reps.append((tuple(points[i] for i in support), coeffs))
            print("  ", gamma, target, reps[:3])


if __name__ == "__main__":
    audit(n=4, k=1, e=1, p=5)
    audit(n=5, k=1, e=1, p=7)
    audit(n=5, k=1, e=2, p=7)
    audit(n=6, k=2, e=2, p=7)
