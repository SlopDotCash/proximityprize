#!/usr/bin/env python3
"""Check signed Paley row budgets, determinant multiplicities, and ternary rank ceilings."""

from itertools import combinations, permutations, product
from math import comb, prod

from probe_paley_shift_multiplicities import determinant, require, translated_coefficients, trim


def characters(p):
    squares = {i*i % p for i in range(1, p)}
    return [0 if i == 0 else 1 if i in squares else -1 for i in range(p)]


def signed_jets(sites, signs, degree, width, p):
    coefficients = [sign * pow(prod(u-v for v in sites if v != u), -1, p)
                    for u, sign in zip(sites, signs)]
    base = [comb(degree, j) * sum(c * pow(u, degree-j, p)
            for c, u in zip(coefficients, sites)) % p for j in range(degree+1)]
    return [trim([base[j] * comb(j, k) * pow(comb(degree, k), -1, p) % p
                  for j in range(k, len(base))]) for k in range(2*width-1)]


def degree_budget(d, a, x, minority):
    return x*(d+a-2*x) - max(0, x-minority)*max(0, a-x-minority)


def check_rows(p):
    """The positive part maximizes the finite budget over all target subsets."""
    chi = characters(p)
    d = (p-1)//2
    checked = determinants = 0
    for a in range(2, d+2):
        for sites in combinations(range(p), a):
            rows = [tuple(chi[(b+u) % p] for u in sites) for b in range(p)]
            zeros = [row.count(0) for row in rows]
            for rest in product((1, -1), repeat=a-1):
                signs = (1, *rest)  # Simultaneously reversing signs preserves all assertions.
                minority = min(signs.count(1), signs.count(-1))
                scores = [sum(u*v for u, v in zip(row, signs)) for row in rows]
                for x in range(1, a//2+1):
                    budget = degree_budget(d, a, x, minority)
                    required = [max(0, val*val-(a-z-2*x)**2) for val, z in zip(scores, zeros)]
                    require(sum(required) <= 4*budget, (p, sites, signs, x, "global budget"))
                    checked += 1
                    if p <= 7 or (sites == tuple(range(a)) and p <= 13):
                        jets = signed_jets(sites, signs, d+a-2, x, p)
                        poly = determinant(jets, x, p)
                        require(bool(poly) and len(poly)-1 <= budget,
                                (p, sites, signs, x, "nonzero determinant and degree"))
                        if minority <= x:
                            require(len(poly)-1 == budget, (p, sites, signs, x, "pivot degrees"))
                        for b, charge in enumerate(required):
                            shifted = translated_coefficients(poly, b, p)
                            order = next(i for i, c in enumerate(shifted) if c)
                            require(4*order >= charge, (p, sites, signs, x, b, "root order"))
                            if x == a//2:
                                require(order == scores[b]**2//4, (p, sites, signs, b, "central order"))
                        determinants += 1
    return checked, determinants


def check_ranks(p):
    chi = characters(p)
    d = (p-1)//2
    permutations_with_sign = [(order, (-1)**sum(order[i] > order[j]
        for i, j in combinations(range(4), 2))) for order in permutations(range(4))]
    singular = set()
    for sites in combinations(range(p), 4):
        value = sum(sgn * prod(chi[(sites[i]-sites[order[i]]) % p] for i in range(4))
                    for order, sgn in permutations_with_sign)
        if value % 3 == 0:
            singular.add(sites)
    checked = 0
    for n in range(3, min(d+2, p)+1):
        for sites in combinations(range(p), n):
            energy = sum(sum(chi[(u-t) % p]*chi[(u-b) % p] for u in sites)**2
                         for t in sites for b in sites)
            count = sum(block in singular for block in combinations(sites, 4))
            require(energy == n*(n-1)*(2*n-3)+8*chi[-1]*(4*count-comb(n,4)),
                    (p, sites, "rank identity"))
            for x in range(1, (n-1)//2+1):
                baseline = (n-1)*(n-2-2*x)**2 + (n-1-2*x)**2
                bound = n * (baseline+4*x*(d+n-1-2*x))
                require(energy <= bound, (p, sites, x, "four-site ceiling"))
            checked += 1
    return checked


if __name__ == "__main__":
    totals = [check_rows(p) for p in (3, 5, 7, 11, 13)]
    rank_domains = sum(check_ranks(p) for p in (3, 5, 7, 11, 13))
    print(f"{sum(a for a, _ in totals):,} signed row budgets, "
          f"{sum(b for _, b in totals):,} polynomial determinants, "
          f"{rank_domains:,} four-site rank domains")
