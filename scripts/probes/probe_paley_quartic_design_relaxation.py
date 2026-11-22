#!/usr/bin/env python3
"""Check exact affine/projective design-slice contractions, PSD and local Boolean events."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, lcm, prod


def pair_psd(matrix):
    """Fraction-free symmetric elimination, including the zero-pivot PSD test."""
    denominator = lcm(*(entry.denominator for row in matrix for entry in row))
    a = [[int(entry * denominator) for entry in row] for row in matrix]
    previous = 1
    for i, row in enumerate(a):
        pivot = row[i]
        if pivot < 0 or (pivot == 0 and any(row[i + 1:])):
            return False
        if not pivot:
            continue
        for j in range(i + 1, len(a)):
            cross = row[j]
            line = a[j]
            for k in range(j, len(a)):
                numerator = pivot * line[k] - cross * row[k]
                value, remainder = divmod(numerator, previous)
                assert remainder == 0
                line[k] = value
        previous = pivot
    return True


def design(p):
    chi = [pow(i, (p-1)//2, p) for i in range(p)]
    chi = [-1 if value == p-1 else value for value in chi]
    def entry(a, b):
        if a == b:
            return 0
        if a == p:
            return 1
        return chi[-1] if b == p else chi[(a-b) % p]
    signs = [(perm, (-1)**sum(perm[i] > perm[j] for i, j in combinations(range(4), 2)))
             for perm in permutations(range(4))]
    singular = set()
    for sites in combinations(range(p+1), 4):
        det = sum(sign * prod(entry(sites[i], sites[perm[i]]) for i in range(4))
                  for perm, sign in signs)
        a, b, c, d = sites
        cycles = sum(entry(i,j)*entry(j,k)*entry(k,l)*entry(l,i)
                     for i,j,k,l in ((a,b,c,d), (a,b,d,c), (a,c,b,d)))
        assert det == 3 - 2*cycles
        assert (det % 3 == 0) == (cycles == 3*chi[-1])
        if det % 3 == 0:
            singular.add(sites)
    num = (p-2-3*chi[-1]) // 4
    counts = Counter(t for block in singular for t in combinations(block, 3))
    assert all(counts[t] == num for t in combinations(range(p+1), 3))
    return singular


def check(p, singular, affine, target, k):
    n = p if affine else p+1
    counts = Counter()
    for sites in combinations(range(n), 4):
        if (sites in singular) == target:
            for i in range(5):
                counts.update(combinations(sites, i))
    moments = {s: Fraction(value * comb(k, 4), counts[()] * comb(k-len(s), 4-len(s)))
               for s, value in counts.items()}
    get = lambda sites: moments.get(tuple(sorted(set(sites))), Fraction())
    assert get(()) == 1
    for t in range(4):
        for s in combinations(range(n), t):
            assert sum(get(s+(v,)) for v in range(n) if v not in s) == (k-t)*get(s)
            if t <= 2 or not affine:
                assert get(s) == Fraction(comb(k,t), comb(n,t))
    assert sum(get(s) for s in combinations(range(n),4) if s in singular) == target * comb(k, 4)
    pairs = list(combinations(range(n), 2))
    gram = [[get(a+b) for b in pairs] for a in pairs]
    psd = pair_psd(gram)
    local = True
    for sites in combinations(range(n), 4):
        masses = []
        for t in range(5):
            for on in combinations(sites, t):
                off = tuple(x for x in sites if x not in on)
                masses.append(sum((-1)**j * get(on+subset) for j in range(5-t)
                                  for subset in combinations(off, j)))
        assert sum(masses) == 1
        local &= min(masses) >= 0
    return psd, local


def check_orbit_compression(p):
    """Exact dilation compression; its characteristic polynomial kills the full cross kernel."""
    chi = [((pow(i, (p-1)//2, p) + 1) % p) - 1 for i in range(p)]
    def sign(a, b):
        if a == b:
            return 0
        if a == p:
            return 1
        return chi[-1] if b == p else chi[(a-b) % p]
    pairs = list(permutations(range(p + 1), 2))
    index = {pair: i for i, pair in enumerate(pairs)}
    cross = [[sign(a,c)*sign(a,d)*sign(b,c)*sign(b,d) for c,d in pairs] for a,b in pairs]
    # Use projective generators, including inversion which interchanges zero and infinity.
    maps = [[(x+1) % p for x in range(p)] + [p], [p] + [pow(x,-1,p) for x in range(1,p)] + [0]]
    maps += [[z*x % p for x in range(p)] + [p] for z in range(1,p)]
    for f in maps:
        perm = [index[(f[i],f[j])] for i,j in pairs]
        assert all(cross[x][y] == cross[u][v]
                   for x,u in enumerate(perm) for y,v in enumerate(perm))
    orbits = [[index[(z*i % p, z*(i+1) % p)] for z in range(1,p)] for i in range(p)]
    orbits += [[index[(0,p)]], [index[(p,0)]],
               [index[(z,p)] for z in range(1,p)], [index[(p,z)] for z in range(1,p)]]
    assert sorted(i for orbit in orbits for i in orbit) == list(range(len(pairs)))
    b = [[sum(cross[row[0]][t] for t in col) for col in orbits] for row in orbits]
    for i in range(p):
        for j in range(p):
            complete = sum(chi[((j*z-i)*(j*z-i-1)*((j+1)*z-i)*((j+1)*z-i-1)) % p]
                           for z in range(p))
            assert b[i][j] == complete - int(i not in (0,p-1))
    # Faddeev-LeVerrier uses integer traces and exact divisions.
    n = len(b)
    coeffs = []
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    for degree in range(1, n + 1):
        power = [[sum(x*y for x,y in zip(row,col)) for col in zip(*power)] for row in b]
        c, rem = divmod(-sum(power[i][i] for i in range(n)), degree)
        assert rem == 0
        coeffs.append(c)
        for i in range(n):
            power[i][i] += c
    assert not any(any(row) for row in power)
    vector = [1] + [0]*(len(pairs)-1)
    for c in coeffs:
        vector = [sum(x*y for x,y in zip(row,vector)) for row in cross]
        vector[0] += c
    assert not any(vector)


def main():
    for p in (5, 7, 11, 13):
        check_orbit_compression(p)
    print("ordered-pair spectrum compression checked at 5, 7, 11, 13")
    cases = [
        # At k=4 these are the genuine distributions on the chosen blocks.
        (7, True, True, 4, True), (7, False, False, 4, True),
        # Finite controls above degree four, in both quadratic congruence classes.
        (11, False, False, 5, True), (13, True, False, 5, True),
        (23, True, True, 5, True),
        # Small p does not permit extrapolation to every slice size.
        (7, True, True, 5, False),
    ]
    blocks = {p: design(p) for p in {case[0] for case in cases}}
    for p, affine, target, k, expected in cases:
        psd, local = check(p, blocks[p], affine, target, k)
        assert psd == expected and (not psd or local)
        print(p, "affine" if affine else "projective", "singular" if target else "nonsingular",
              "k", k, "PSD", psd, "local probabilities", local)


if __name__ == "__main__":
    main()
