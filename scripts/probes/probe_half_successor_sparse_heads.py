"""Verify full-size sparsity bounds and the dyadic moment count over finite fields."""
from itertools import combinations, product
from math import comb, prod
from random import Random

from probe_punctured_affine_locators import A, B, PRIME, TARGETS, evaluate


def arithmetic():
    n = 1 << 30
    assert comb(23_170, 2) < n // 4 <= comb(23_171, 2)
    assert 16_384 ** 2 == n // 4
    for terms, pair, required in [(336, 224, n // 2), (372, 248, 3*n // 4), (400, 267, n)]:
        assert comb(terms + 2, 4) < required <= comb(terms + 3, 4)
        assert 5 * comb(pair + 2, 4) < required <= 5 * comb(pair + 3, 4)
    vertices = frozenset(range(4))
    edges = list(map(frozenset, combinations(vertices, 2)))
    profiles = [([], edges[:-1]), ([{0, 1, 2}], [e for e in edges if 3 in e]), ([], edges)]
    for triple_sites, double_sites in profiles:
        for pair in edges:
            complement = vertices - pair
            exceptions = 1 + int(len(double_sites) == 6)
            for errors in triple_sites + double_sites:
                exceptions += bool(errors & pair) and bool(errors & complement)
            assert exceptions <= 6


def check_moments(n, values, prime, root):
    assert pow(root, n // 2, prime) == prime - 1
    weights = [(x, v) for x, v in zip((pow(root, j, prime) for j in range(n)), values) if v]
    count = len(weights)
    moments = [sum(v * pow(x, -j, prime) for x, v in weights) % prime for j in range(n)]
    assert sum(bool(v) for v in moments) >= n // (1 << (count.bit_length() - 1))
    if count <= 6:
        for u in range(1, n, 2):
            for first in range(n):
                assert any(moments[(first + u*j) % n] for j in range(count))
    return [c * pow(n, -1, prime) % prime for c in moments]


def concrete_witness():
    n, p = 16, PRIME
    sites = [pow(3, j, p) for j in range(n)]
    heads = ((), (8, 10, 11, 12, 13, 16), (7, 8, 9, 10, 15, 16), (6, 7, 8, 11, 12, 15))
    scales = (0, 1, 11, 5)
    words = [[c * prod(x-y for y in roots) % p for x in sites]
             for c, roots in zip(scales, heads)]
    for a, b, c, d in ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)):
        values = [(x-y)*(z-t) % p for x, y, z, t in zip(words[a], words[b], words[c], words[d])]
        assert 4 <= sum(bool(v) for v in values) <= 6
        coeffs = check_moments(n, values, p, 3)
        assert len([j for j, v in enumerate(coeffs) if v]) >= n // 4
        assert coeffs[n - 3:] == [0, 0, 0]

    values = [prod(evaluate(A, x) + s*(x-z)*evaluate(B, x) for s, z in TARGETS) % p
              for x in sites]
    support = [j for j, v in enumerate(values) if v]
    assert 0 in support and len(support) <= 2
    coeffs = check_moments(n, values, p, 3)
    assert all(sum(c * pow(x, j, p) for j, c in enumerate(coeffs)) % p == v
               for x, v in zip(sites, values))


def controls():
    root = 4  # order four in F_17
    for values in product(range(17), repeat=4):
        if any(values):
            check_moments(4, values, 17, root)
    rng = Random(129)
    for n in (8, 16, 32, 64):
        root = pow(3, 256 // n, 257)
        for support_size in range(1, min(9, n + 1)):
            for _ in range(6):
                values = [0] * n
                for j in rng.sample(range(n), support_size):
                    values[j] = rng.randrange(1, 257)
                check_moments(n, values, 257, root)


if __name__ == '__main__':
    arithmetic()
    concrete_witness()
    controls()
    print('Punctured matching products, affine locators and dyadic Fourier bounds verified.')
