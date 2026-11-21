#!/usr/bin/env python3
"""Test three disjoint degree-nine fibers on mu_32 in characteristic zero.

The dyadic valuation test is exact in Q(zeta_32). It only discards
characteristic-zero configurations. The remaining tests use a split prime.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import product


N, D, P = 32, 9, 97
HOLES = N - 3 * D


def merge_state(left, right, size):
    """Merge counts and color potentials from the two parity classes."""
    a, v = left
    b, w = right
    counts = tuple(x + y for x, y in zip(a, b))
    if max(counts) > D or size - sum(counts) > HOLES:
        return None
    values = []
    for i in range(3):
        j, k = (i + 1) % 3, (i + 2) % 3
        x = 2 * v[i] + b[j] - b[k] if a[i] else None
        y = 2 * w[i] + a[j] - a[k] if b[i] else None
        if x is not None and y is not None and x != y:
            return None
        values.append(y if x is None else x)
    return counts, tuple(values)


def dyadic_table():
    leaves = []
    for label in range(4):
        counts = tuple(int(i == label) for i in range(3))
        values = tuple(0 if i == label else None for i in range(3))
        leaves.append((counts, values))
    ways = Counter(leaves)
    parents = {}
    size = 2
    while size <= N:
        table = defaultdict(list)
        next_ways = Counter()
        for left, right in product(ways, repeat=2):
            z = merge_state(left, right, size)
            if z is not None:
                table[z].append((left, right))
                next_ways[z] += ways[left] * ways[right]
        parents[size] = table
        ways = next_ways
        print(f"size {size}: {len(ways)} states, {sum(ways.values())} colorings")
        size *= 2
    return parents, ways


def spread(x):
    """Move bit j of a child mask to bit 2j of its parent."""
    y = 0
    while x:
        bit = x & -x
        y |= bit * bit
        x -= bit
    return y


def valuation_survivors(parents, ways):
    # A uniquely zero potential distinguishes color A. Colors B and C may
    # be exchanged, and rotation can send an omitted site to exponent zero.
    if any(state[1].count(0) != 1 for state in ways):
        raise ArithmeticError("a root state lacks the claimed unique zero potential")

    @cache
    def masks(size, state):
        if size == 1:
            return [state[0]]
        return [(a | (u << 1), b | (v << 1), c | (w << 1))
                for left, right in parents[size][state]
                for a, b, c in even_masks(size // 2, left)
                for u, v, w in even_masks(size // 2, right)]

    @cache
    def even_masks(size, state):
        return [(spread(a), spread(b), spread(c)) for a, b, c in masks(size, state)]

    for state in ways:
        if state[1][0] != 0:
            continue
        for left, right in parents[N][state]:
            odds = [(x << 1, y << 1, z << 1) for x, y, z in even_masks(N // 2, right)]
            for a, b, c in even_masks(N // 2, left):
                if (a | b | c) & 1:
                    continue
                for u, v, w in odds:
                    if (b | v) < (c | w):
                        yield a | u, b | v, c | w


def evaluations():
    """All products at a fixed root, for masks in either half of the array."""
    z = pow(5, (P - 1) // N, P)
    sites = [pow(z, i, P) for i in range(N)]
    if len(set(sites)) != N:
        raise ArithmeticError("incorrect order of reference root")
    tables = []
    for offset in (0, N // 2):
        rows = []
        for x in sites:
            products = bytearray(1 << (N // 2))
            products[0] = 1
            for mask in range(1, len(products)):
                bit = mask & -mask
                y = sites[offset + bit.bit_length() - 1]
                products[mask] = products[mask ^ bit] * (x - y) % P
            rows.append(products)
        tables.append(rows)
    return tables


def main():
    parents, ways = dyadic_table()
    lo, hi = evaluations()
    cut = (1 << (N // 2)) - 1
    scanned = 0
    candidates = []
    for a, b, c in valuation_survivors(parents, ways):
        scanned += 1
        al, ah, bl, bh = a & cut, a >> 16, b & cut, b >> 16
        first = c & -c
        x = first.bit_length() - 1
        fa = lo[x][al] * hi[x][ah] % P
        fb = lo[x][bl] * hi[x][bh] % P
        others = c ^ first
        while others:
            bit = others & -others
            y = bit.bit_length() - 1
            if (fa * lo[y][bl] * hi[y][bh] - fb * lo[y][al] * hi[y][ah]) % P:
                break
            others ^= bit
        else:
            candidates.append((a, b, c))
    print(f"{scanned} unordered partitions with a fixed omitted site pass the valuation test")
    print(f"{len(candidates)} survive the reduction modulo {P}")
    if candidates:
        raise ArithmeticError(f"unexpected surviving triples: {candidates[:20]}")
    if scanned != 1575040:
        raise ArithmeticError("unexpected number of valuation survivors")
    if 6 * N * scanned != HOLES * sum(ways.values()):
        raise ArithmeticError("incomplete normalized coloring count")


if __name__ == "__main__":
    main()
