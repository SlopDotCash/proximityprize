#!/usr/bin/env python3
"""Check the unit-comparison lower bound for seven complete blocks modulo 16."""
import argparse
from functools import lru_cache
from fractions import Fraction
from itertools import combinations

from probe_mu64_unit_lattice import require

SITES = frozenset(range(16))


@lru_cache(None)
def comparison_rows(centers):
    """All primitive-unit coordinates for every unordered center pair."""
    rows = []
    for x, y in combinations(centers, 2):
        for r in (1, 3, 5, 7):
            row = [0]*16
            for k in range(4):
                for s in (1, -1):
                    step = s*(r << k)
                    row[(y+step) % 16] += 1
                    row[(x+step) % 16] -= 1
            rows.append(row)
    return rows


def gaps(centers, positive, negative, unused):
    """Integer numerator and denominator of each lower bound for V/q²."""
    weights = [0]*16
    for j in positive:
        weights[j] = 9
    for j in negative:
        weights[j] = -9
    for j in unused:
        weights[j] = len(negative)-len(positive)
    for row in comparison_rows(centers):
        difference = sum(a*b for a, b in zip(row, weights))
        if difference:
            variance = 9*sum(row[j]**2 for j in unused) - sum(row[j] for j in unused)**2
            require(variance >= 0, "negative sum of squares")
            yield difference**2, 18*variance


def first_triples(full):
    triples = combinations(range(16), 3)
    if full:
        return triples
    return sorted({min(tuple(sorted((a*x+b) % 16 for x in triple))
                       for a in range(1,16,2) for b in range(16)) for triple in triples})


def check(full):
    seen = equalities = 0
    sharp = False
    for triple in first_triples(full):
        for first in combinations(sorted(SITES.difference(triple)), 2):
            for second in combinations(sorted(SITES.difference(triple,first)), 2):
                if first >= second:
                    continue
                unused = SITES.difference(triple, first, second)
                maximum = None
                seen += 1
                for centers, positive, negative in ((triple, first, second),
                                                  (first, triple, second), (second, triple, first)):
                    for numerator, denominator in gaps(centers, positive, negative, unused):
                        if denominator == 0 or 99*numerator > 8*denominator:
                            maximum = True
                            break
                        if 99*numerator == 8*denominator:
                            maximum = False
                    if maximum is True:
                        break
                require(maximum is not None, f"layout below 8/99: {triple}, {first}, {second}")
                if maximum is False:
                    equalities += 1
                    sharp = True
    require(sharp, "minimum not attained")
    expected = 1201200 if full else 19305
    require(seen == expected, f"layout coverage: {seen} != {expected}")
    print(f"{seen} layouts, minimum largest comparison bound {Fraction(8,99)}, "
          f"{equalities} attaining layouts")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all-layouts', action='store_true', help='also visit the affine copies')
    check(parser.parse_args().all_layouts)
