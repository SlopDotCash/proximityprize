#!/usr/bin/env python3
"""Check the four-site rank design and its fixed-size variance with the infinity site included."""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, prod


def check(prime):
    v = prime + 1
    chi = [pow(x, (prime - 1)//2, prime) for x in range(prime)]
    chi = [-1 if x == prime-1 else x for x in chi]
    e = chi[-1]

    def entry(x, y):
        if x == y:
            return 0
        if x == prime:
            return 1
        if y == prime:
            return e
        return chi[(x-y) % prime]

    matrix = [[entry(x, y) for y in range(v)] for x in range(v)]
    terms = [(perm, (-1)**sum(perm[i] > perm[j] for i, j in combinations(range(4), 2)))
             for perm in permutations(range(4))]
    counts = [0]*(1 << v)
    triple_counts = {}
    for sites in combinations(range(v), 4):
        det = sum(sign*prod(matrix[sites[i]][sites[perm[i]]] for i in range(4))
                  for perm, sign in terms)
        if det not in (3-6*e, 3+2*e):
            raise ArithmeticError((prime, sites, det))
        block = int(det % 3 == 0)
        counts[sum(1 << x for x in sites)] = block
        for triple in combinations(sites, 3):
            triple_counts[triple] = triple_counts.get(triple, 0) + block
    if set(triple_counts.values()) != {(prime-2-3*e)//4}:
        raise ArithmeticError("projective triple completions")
    # The subset zeta transform counts the blocks contained in each mask.
    for x in range(v):
        bit = 1 << x
        for base in range(0, len(counts), 2*bit):
            for offset in range(bit):
                counts[base+bit+offset] += counts[base+offset]

    sums = [0]*(v+1)
    squares = [0]*(v+1)
    theta = Fraction(prime-2-3*e, 4*(prime-2))
    for mask, count in enumerate(counts):
        m = mask.bit_count()
        sums[m] += count
        squares[m] += count**2
        if mask % 997 == 0 or mask == (1 << v)-1:
            sites = [x for x in range(v) if mask & (1 << x)]
            energy = sum(sum(matrix[x][t]*matrix[x][y] for x in sites)**2
                         for t in sites for y in sites)
            if energy != m*(m-1)*(2*m-3) + 8*e*(4*count - comb(m, 4)):
                raise ArithmeticError(("energy", prime, mask))
    for m in range(v+1):
        mean = Fraction(sums[m], comb(v, m))
        variance = Fraction(squares[m], comb(v, m)) - mean**2
        expected = theta*(1-theta)*comb(m, 4)*Fraction(comb(v-m, 4), comb(v-4, 4))
        if mean != theta*comb(m, 4) or variance != expected:
            raise ArithmeticError(("slice", prime, m, mean, variance))
    return len(counts)


if __name__ == "__main__":
    total = sum(check(p) for p in (7, 11, 13, 17))
    print(f"Four-site rank design means and variances checked on {total} projective domains")
