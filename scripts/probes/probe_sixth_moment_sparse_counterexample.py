#!/usr/bin/env python3
"""Exact examples separating the repeated-entry tests from the full sixth moment."""

from collections import Counter, defaultdict
from itertools import combinations
from math import isqrt


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify(n, p, g):
    require(p > 2 and all(p % k for k in range(2, isqrt(p) + 1)), "nonprime modulus")
    roots = [pow(g, i, p) for i in range(n)]
    require(n & (n - 1) == 0 and len(set(roots)) == n and pow(g, n, p) == 1, "wrong order")
    signs = {pow(x - 1, n, p) for x in roots[1:n // 2 + 1]}
    require(len(signs) == n // 2, "Sidon test failed")
    require(all(s * pow(2, n, p) % p not in signs for s in signs), "doubled collision")
    require(pow(3, n, p) != 1, "3 belongs to the subgroup")
    require(all(pow(3 - x, n, p) not in signs for x in roots[1:]), "triple collision")

    # First count all ordered triples directly in the prime field.
    pairs = Counter((x + y) % p for x in roots for y in roots)
    triples = Counter()
    for s, count in pairs.items():
        for z in roots:
            triples[(s + z) % p] += count
    energy = sum(count * count for count in triples.values())
    require(sum(count * count for count in pairs.values()) == 3 * n * (n - 1), "fourth moment")

    # Independently count triples according to the coset of 1 + x + y.
    # Its multiplicity at each *element* of a nonzero coset equals the
    # normalized pair count. The single zero receives n times its count.
    cosets = Counter(pow(1 + x + y, n, p) for x in roots for y in roots)
    zero = cosets.pop(0, 0)
    orbit_energy = (n * zero) ** 2 + n * sum(count**2 for count in cosets.values())
    require(orbit_energy == energy, "normalization mismatch")

    # Count both remaining orbit types without using either energy calculation.
    # Rotate a repeated element (five classes) or any element (six classes) to 1.
    available = [i for i in range(1, n) if i != n // 2]
    def antipode_free(indices):
        return len({i % (n // 2) for i in indices}) == len(indices)
    pair_sums = defaultdict(list)
    for i, j in combinations(available, 2):
        if antipode_free((i, j)):
            pair_sums[(roots[i] + roots[j]) % p].append((i, j))
    def anchored(tail_size, target):
        total = 0
        for tail in combinations(available, tail_size):
            if not antipode_free(tail):
                continue
            missing = (target - sum(roots[i] for i in tail)) % p
            for i, j in pair_sums.get(missing, ()):
                if j < tail[0] and antipode_free((i, j) + tail):
                    total += 1
        return total
    five = anchored(2, -2)
    six_anchored = anchored(3, -1)
    require(six_anchored % 6 == 0, "incomplete rotation orbit")
    six = six_anchored // 6
    pairable = 15 * n**3 - 45 * n**2 + 40 * n
    require(energy == pairable + 360 * n * (five + 2 * six), "sextuple orbit count")
    margin = p * (energy - 15 * n**3) - n**6
    print(f"n={n} p={p} g={g} E3={energy} A5={five} A6={six} signed_Wick_margin={margin}")
    return margin


if __name__ == "__main__":
    require(verify(32, 11617, 3115) < 0, "six-class control")
    require(verify(32, 13217, 4477) < 0, "five-class control")
    require(verify(64, 173249, 121218) > 0, "first counterexample")
    require(64**5 < 40 * 81818497, "large-field comparison")
    require(verify(64, 81818497, 76240642) > 0, "large-field counterexample")
    require(verify(128, 766721, 656707) > 0, "second counterexample")
