#!/usr/bin/env python3
"""Compute all closed-ball list histograms by ranks of RS syndrome subspaces."""

from collections import Counter
from itertools import combinations, product
from math import comb


def require(condition, message):
    if not condition:
        raise ValueError(message)


def vanisher(sites, p):
    coeff = [1]
    for x in sites:
        nxt = [0] * (len(coeff) + 1)
        for i, a in enumerate(coeff):
            nxt[i] = (nxt[i] - x * a) % p
            nxt[i + 1] = (nxt[i + 1] + a) % p
        coeff = nxt
    return tuple(coeff)


def reduce_row(row, basis, p):
    """Reduce a normal against a canonical row-echelon basis."""
    for pivot, normal in basis:
        value = row[pivot]
        if value:
            row = tuple((x - value * y) % p for x, y in zip(row, normal))
    return row


def extend_basis(basis, reduced, p):
    pivot = next(i for i, value in enumerate(reduced) if value)
    inverse = pow(reduced[pivot], -1, p)
    normal = tuple(value * inverse % p for value in reduced)
    prior = tuple((i, reduce_row(row, ((pivot, normal),), p)) for i, row in basis)
    return tuple(sorted((*prior, (pivot, normal))))


def flat_masks(domain, k, p):
    """Group syndrome flats by dimension. Bits indicate containing hyperplanes."""
    n = len(domain)
    r = n - k
    require(0 < k < n and len(set(x % p for x in domain)) == n, "RS parameters")
    supports = list(combinations(range(n), r - 1))
    normals = [vanisher((domain[i] for i in support), p) for support in supports]
    levels = {0: [(1 << len(normals)) - 1]}
    bases = {()}
    for rank in range(r):
        masks, children = [], set()
        for basis in bases:
            mask = 0
            for i, normal in enumerate(normals):
                reduced = reduce_row(normal, basis, p)
                if not any(reduced):
                    mask |= 1 << i
                elif rank + 1 < r:
                    children.add(extend_basis(basis, reduced, p))
            masks.append(mask)
        require(len(set(masks)) == len(masks), "different bases identified one flat")
        levels[r - rank] = masks
        bases = children
    return supports, levels


def list_histograms(domain, k, p, width):
    """Distribution over syndromes; each syndrome has Q**k received centers."""
    n, r, Q = len(domain), len(domain) - k, p**width
    require(width >= 1, "positive width")
    hyperplanes, levels = flat_masks(domain, k, p)
    support_masks = [Counter() for _ in range(n + 1)]
    for j in range(r):
        for support in combinations(range(n), j):
            mask = sum(1 << i for i, H in enumerate(hyperplanes) if set(support) <= set(H))
            support_masks[j][mask] += 1
    for j in range(r, n + 1):
        support_masks[j][0] = comb(n, j)

    strata = []
    histograms = [Counter() for _ in range(n + 1)]
    for dimension in range(r + 1):
        layer = []
        for flat in levels[dimension]:
            population = Q**dimension - sum(count for sub, count in strata if sub & flat == flat)
            require(population >= 0, "negative stratum count")
            layer.append((flat, population))
            if not population:
                continue
            supported = [
                Q**max(0, j - r) * sum(multiplicity for mask, multiplicity in counts.items()
                                     if flat & mask == mask)
                for j, counts in enumerate(support_masks)
            ]
            for e in range(n):
                size = sum((-1)**(e - j) * comb(n - j - 1, e - j) * supported[j] for j in range(e + 1))
                require(size >= 0, "negative list size")
                histograms[e][size] += population
            histograms[n][Q**k] += population
        strata.extend(layer)
    require(all(sum(h.values()) == Q**r for h in histograms), "incomplete syndrome partition")
    return [len(levels[i]) for i in range(r + 1)], histograms


def exhaustive(domain, k, p, width):
    """Independent small-field check by enumerating all errors and syndromes."""
    n, r = len(domain), len(domain) - k
    columns = [tuple(pow(x, i, p) for i in range(r)) for x in domain]
    weights = [Counter() for _ in range(n + 1)]
    alphabet = tuple(product(range(p), repeat=width))
    for word in product(alphabet, repeat=n):
        wt = sum(any(x) for x in word)
        syndrome = tuple(sum(symbol[row] * h[i] for symbol, h in zip(word, columns)) % p
                         for row in range(width) for i in range(r))
        for e in range(wt, n + 1):
            weights[e][syndrome] += 1
    hists = [Counter(counts.values()) for counts in weights]
    for h in hists:
        missing = p**(width * r) - sum(h.values())
        if missing:
            h[0] = missing
    return hists


def check_characteristic_three():
    # F_9 = F_3[u]/(u^2 + 1). A triple contains the syndrome (0,0,1,0)
    # exactly when the X^2 coefficient of its locator, minus its sum, is zero.
    sites = set(product(range(3), repeat=2)) - {(0, 0)}
    triples = [
        triple for triple in combinations(sites, 3)
        if all(sum(site[i] for site in triple) % 3 == 0 for i in range(2))
    ]
    require(len(triples) == 8, "characteristic-three triple count")
    degrees = Counter(site for triple in triples for site in triple)
    require(set(degrees.values()) == {3}, "characteristic-three degree")
    pairs = [frozenset(pair) for triple in triples for pair in combinations(triple, 2)]
    require(len(set(pairs)) == 24, "characteristic-three repeated pair")


def main():
    cases = [
        (3, [0, 1, 2], 2, 1),
        (3, [0, 1, 2], 1, 1),
        (3, [0, 1, 2], 1, 2),
        (7, [0, 1, 2, 3, 4], 2, 1),
    ]
    for p, domain, k, width in cases:
        _, actual = list_histograms(domain, k, p, width)
        expected = exhaustive(domain, k, p, width)
        require(actual == expected, "direct enumeration disagrees")
    check_characteristic_three()
    for n in (5, 6):
        p = 31
        generator = pow(3, (p - 1) // n, p)
        domain = [pow(generator, i, p) for i in range(n)]
        for width in (1, 2):
            _, histograms = list_histograms(domain, n - 3, p, width)
            require([max(h) for h in histograms[:4]] == [1, 1, n // 2, comb(n, 3)],
                    "redundancy-three profile")

    p = 2**64 - 2**32 + 1
    require(pow(7, (p - 1) // 2, p) == p - 1, "Proth witness")
    omega = pow(7, (p - 1) // 8, p)
    require(pow(omega, 4, p) == p - 1, "primitive eighth root")
    domain = [pow(omega, j, p) for j in range(8)]
    for width in (1, 2):
        Q = p**width
        levels, histograms = list_histograms(domain, 4, p, width)
        require(levels == [1, 5184, 988, 56, 1], "octagon intersection lattice")
        spectrum = sorted(histograms[3])
        require(spectrum == [0, 1, 2, 3, 4, 5, 7], "three-error spectrum")
        require(histograms[3][7] == 8 * (Q - 1), "number of maximizing syndromes")
        require([max(h) for h in histograms[:5]] == [1, 1, 1, 7, 70], "list thresholds")
        require(max(histograms[5]) >= 1 + 56 * (Q - 1), "three-root cubic lower bound")
        print(f"Goldilocks width {width}: flats {levels}, three-error lists {spectrum}, "
              "maximizing syndromes 8(Q-1)")
    print("All tiny histograms and the characteristic-three incidence check passed.")


if __name__ == "__main__":
    main()
