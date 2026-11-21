#!/usr/bin/env python3
"""Check an integral witness for four cubic RS words with 12 agreements on mu_32."""
from itertools import combinations
from probe_mu16_quintic_fibers import multiply, subtract

N = 32
ONE = (1,) + (0,) * 15
ZERO = (0,) * 16
# A[ij] records the sites on which the words i,j must coincide.
PAIRS = {(0, 1): (0, 1, 2), (0, 2): (7, 9, 23), (0, 3): (11, 25, 27),
         (1, 2): (6, 20), (1, 3): (14, 28), (2, 3): (13, 17, 21)}
PRIVATE = ((3, 4, 5), (8, 10, 12, 15, 16), (18, 19, 22, 24), (26, 29, 30, 31))


def root(j):
    return tuple((1 if j < 16 else -1) if k == j % 16 else 0 for k in range(16))


def value(roots, j):
    v = ONE
    for s in roots:
        v = multiply(v, subtract(root(j), root(s)))
    return v


def verify():
    # Common scaling clears both denominators. Each factor in these constants
    # is a difference of distinct roots, a unit after inverting 2.
    a, b, c = [PAIRS[(0, i)] for i in (1, 2, 3)]
    ca = multiply(value(b, 6), value(c, 14))
    cb = multiply(value(a, 6), value(c, 14))
    cc = multiply(value(a, 14), value(b, 6))
    sites_used = []
    agreements = [set(vals) for vals in PRIVATE]
    values = [[ZERO, multiply(ca, value(a, j)), multiply(cb, value(b, j)),
               multiply(cc, value(c, j))] for j in range(N)]
    for (h, k), js in PAIRS.items():
        for j in js:
            if values[j][h] != values[j][k]:
                raise ArithmeticError(f"false equality between {h},{k} at {j}")
            sites_used.append(j)
            agreements[h].add(j)
            agreements[k].add(j)
    sites_used.extend(j for js in PRIVATE for j in js)
    if sorted(sites_used) != list(range(N)) or any(len(s) != 12 for s in agreements):
        raise ArithmeticError("incorrect center allocation")
    # The three nonzero cubics have different, pairwise-disjoint root sets.
    if not all(set(x).isdisjoint(y) for x, y in combinations((a, b, c), 2)):
        raise ArithmeticError("root sets do not distinguish the cubics")
    if 4 * 13 <= N + 6 * 3:
        raise ArithmeticError("pair-count upper bound failed")
    print("Integral identities verified in Z[z]/(z^16+1)")
    print("RS[32,4] on mu_32: four words achieve 12 agreements; 13 are impossible")


if __name__ == "__main__":
    verify()
