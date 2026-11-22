#!/usr/bin/env python3
"""Count completely split cubic fibers in pencils on the order-64 subgroup."""
import argparse
from collections import Counter
from itertools import combinations
from math import comb

FIELDS = {
    "screen": 65537,
    "first": 365375409332725729550921208179070755120141565953,
    "second": 730750818665451459101842416358141509841924915201,
}
ORDER = 64


def canonical(triple):
    """Translate one root to 1 and allow inversion of all three roots."""
    return min(tuple(sorted(sign * (i - first) % ORDER for i in triple))
               for first in triple for sign in (1, -1))


def coefficients(roots, triple, prime):
    a, b, c = (roots[i] for i in triple)
    return (a + b + c) % prime, (a*b + b*c + c*a) % prime, a*b*c % prime


def largest_fiber_count(prime):
    generator = next(g for a in range(2, prime)
                     if pow(g := pow(a, (prime - 1) // ORDER, prime), ORDER // 2, prime) != 1)
    roots = [pow(generator, i, prime) for i in range(ORDER)]
    assert pow(generator, ORDER, prime) == 1 and len(set(roots)) == ORDER
    triples = list(combinations(range(ORDER), 3))
    scores = [coefficients(roots, triple, prime) for triple in triples]
    masks = [sum(1 << i for i in triple) for triple in triples]
    orbit_count = comparisons = maximum = 0
    for j, triple in enumerate(triples):
        if triple != canonical(triple):
            continue
        orbit_count += 1
        a, b, c = scores[j]
        rows = []
        prefix = 1
        for mask, (x, y, z) in zip(masks, scores):
            if mask & masks[j]:
                continue
            u, v, w = (x - a) % prime, (y - b) % prime, (z - c) % prime
            pivot = u or v or w
            assert pivot
            rows.append((u, v, w, pivot, prefix))
            prefix = prefix * pivot % prime
        comparisons += len(rows)
        # Batch inversion normalizes all projective directions with one inversion.
        product_inverse = pow(prefix, -1, prime)
        counts = Counter()
        for u, v, w, pivot, prefix in reversed(rows):
            inverse = product_inverse * prefix % prime
            counts[(u*inverse % prime, v*inverse % prime, w*inverse % prime)] += 1
            product_inverse = product_inverse * pivot % prime
        maximum = max(maximum, 1 + max(counts.values()))
    assert comparisons == orbit_count * comb(ORDER - 3, 3)
    return orbit_count, comparisons, maximum


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--field", choices=FIELDS, default="screen")
    args = parser.parse_args()
    prime = FIELDS[args.field]
    orbit_count, comparisons, maximum = largest_fiber_count(prime)
    print(f"p={prime} orbits={orbit_count} comparisons={comparisons} max_split_fibers={maximum}")
    assert maximum == 3
