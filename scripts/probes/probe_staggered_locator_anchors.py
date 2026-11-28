#!/usr/bin/env python3
"""Verify eighth-rate lists on both named primes with nine and ten serving fibers."""

from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import gcd
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from probe_oriented_fiber_lists import oriented_counter
from probe_quarter_coset_lists import require
from probe_reciprocal_fiber_lists import signature_of
from probe_rotated_locator_union import LENGTH, PRIMES, SOURCE, check_signed_factors, overlaps


@lru_cache(None)
def oriented_cuts(order, node):
    singletons = [(node,), (order-node,)]
    if node % 2:
        return singletons
    return singletons + [left + right for left in oriented_cuts(order, node//2)
                         for right in oriented_cuts(order, (order-node)//2)]


@lru_cache(None)
def uniform_intersection(order, omitted_step, shift, size, residue):
    """Both anchors have all-ones vectors, and all multiples of omitted_step are absent."""
    @lru_cache(None)
    def other_leaves(exponent):
        vector = signature_of({(exponent - shift) % order}, order)
        return sum(entry << i for i, entry in enumerate(vector))

    def classes(node):
        out = Counter()
        for roots in oriented_cuts(order, node):
            mask = 0
            for x in roots:
                covered = other_leaves(x)
                if mask & covered:
                    break
                mask |= covered
            else:
                out[mask, len(roots), sum(roots) % order] += 1
        return out

    def half(nodes):
        table = {(0, 0, 0): 1}
        for node in nodes:
            joined = Counter()
            for (leaves, degree, product), weight in table.items():
                for (other, d, e), multiplicity in local[node].items():
                    if not leaves & other and degree + d <= size:
                        joined[leaves | other, degree+d, (product+e) % order] += weight*multiplicity
            table = joined
        return table

    nodes = list(range(omitted_step//2, order//2, omitted_step))
    local = {node: classes(node) for node in nodes}
    middle = len(nodes)//2
    left, right = half(nodes[:middle]), half(nodes[middle:])
    all_leaves = (1 << (order//4)) - 1
    return sum(w * right.get((all_leaves ^ m, size-d, (residue-e) % order), 0)
               for (m, d, e), w in left.items())


def small_control():
    order, step, size, shift = 32, 4, 5, 4
    ones = (1,) * (order//4)
    exact = Counter()
    for roots in combinations([j for j in range(order) if j % step], size):
        if signature_of(set(roots), order) == ones and (
                signature_of({(x-shift) % order for x in roots}, order) == ones):
            exact[sum(roots) % order] += 1
    require(exact and all(uniform_intersection(order, step, shift, size, r) == exact[r]
                          for r in range(order)), 'small uniform-intersection board')
    print(f'Order {order}: checked every product against all ordinary subsets of size {size}.')


def primary_vectors():
    out = {(1,)*32}
    for length in (4, 8):
        for start in range(0, 32, length):
            out.add(tuple(2 if start <= i < start+length else 1 for i in range(32)))
    return out


def production(binary):
    order, size, root = 128, 17, 8
    h, regular = LENGTH//order, list(range(0, order, 16))
    anchors = [*regular, 8]
    primary = [set() for _ in regular]
    total = 0
    for a in anchors:
        ban = {(s-a) % order for s in anchors} | {64}
        counter = oriented_counter(order, size, ban)
        residue = (root-size*a) % order
        vectors = [(1,)*32] if a == 8 else primary_vectors()
        ranked = []
        for v in vectors:
            histogram = counter(v)
            ranked.extend((histogram[e], v, e) for e in (residue, residue+order))
        chosen = sorted(ranked, reverse=True)[:2 if a == 8 else 9]
        total += sum(w for w, _, _ in chosen)
        if a != 8:
            primary[a//16].update((v, e) for _, v, e in chosen)
    require(all((1,)*32 in {v for v, e in row} and all(sum(v) >= 32 for v, e in row)
                for row in primary), 'regular weights')
    original_pairs = sum(overlaps(binary, order, 8, size, root, primary).values())
    mixed = uniform_intersection(128, 8, 8, 17, 0)
    words = total-original_pairs-8*mixed
    gain = 906876
    require(9*gain <= h and 74*gain + h-1 <= 9*h, 'nine-fiber capacities')
    errors = LENGTH - (18*h-1+gain)
    require((total, original_pairs, mixed, words, errors) ==
            (2159232164, 1736356, 146, 2157494640, 921840005), 'second-prime count')
    require(words > PRIMES[1]//2**128, 'strict second-prime budget')
    print(f'{total} incidences, at most {original_pairs} regular pairs and {8*mixed} mixed pairs. '
          f'At least {words} distinct words within {errors} errors.')


def exceptional_populations(anchor):
    """Remove coarse patterns that can give a regular weight of 32 or 40."""
    special = (16, 32, 48, 80, 96, 112)
    counts = {size: oriented_counter(128, 17-size, range(0, 128, 8)) for size in (2, 3, 4)}
    residue = (8-17*anchor) % 128
    lost = 0
    for size, counter in counts.items():
        for roots in combinations(special, size):
            difference = sum(gcd(x, 128)-8 for x in roots)
            if difference != 32 and (difference != 24 or size != 3):
                continue
            remaining = tuple(2-x for x in signature_of(roots, 128))
            if min(remaining) >= 0:
                histogram = counter(remaining)
                lost += sum(histogram[(e-sum(roots)) % 256] for e in (residue, residue+128))
    return lost


def one_block_residual_bound():
    """Sixteen-root mixed intersections after one exceptional exponent ±32."""
    one = sum(1 << (4*i) for i in range(32))
    high = 8*one
    blocks = [sum(1 << (4*i) for i in range(j, j+8)) for j in range(0, 32, 8)]

    @lru_cache(None)
    def contribution(root):
        return sum(k << (4*i) for i, k in enumerate(signature_of({(root-8) % 128}, 128)))

    def half(nodes):
        table = {(0, 0, 0): 1}
        for node in nodes:
            local = Counter((sum(contribution(x) for x in roots), len(roots), sum(roots) % 128)
                            for roots in oriented_cuts(128, node))
            joined = Counter()
            for (p, d, e), w in table.items():
                for (q, h, f), z in local.items():
                    value = p+q
                    # The other half occupies at least one node in each of four trees.
                    if d+h > 12 or (high+2*one-value) & high != high:
                        continue
                    doubled = (value >> 1) & one
                    if sum(bool(doubled & block) for block in blocks) > 1:
                        continue
                    joined[value, d+h, (e+f) % 128] += w*z
            table = joined
        return table

    left = half((4, 12, 20, 28))
    right = half((36, 44, 52, 60))
    upper = 0
    for target in {one+x-y for x in blocks for y in blocks}:
        totals = Counter()
        for (value, size, exponent), weight in left.items():
            if (high+target-value) & high != high:
                continue
            for residue in (32, 96):
                totals[residue] += weight*right.get((target-value, 16-size,
                                                     (residue-exponent) % 128), 0)
        upper = max(upper, *totals.values())
    return upper


def ten_anchors(binary):
    order, size, h = 128, 17, LENGTH//128
    regular = list(range(0, order, 16))
    extra = (8, 72)
    anchors = sorted([*regular, *extra])
    uniform = (1,)*32
    new_vectors = {uniform, (2,)*32}
    for start in range(0, 32, 2):
        new_vectors.add(tuple(1 if start <= i < start+2 else 2 for i in range(32)))
    rows = []
    for anchor in anchors:
        count = oriented_counter(order, size, {(s-anchor) % order for s in anchors})
        residue = (8-size*anchor) % order
        ranked = []
        for v in new_vectors if anchor in extra else primary_vectors():
            hist = count(v)
            ranked.extend((hist[e], v, e, anchor) for e in (residue, residue+128))
        rows.append(sorted(ranked, reverse=True))

    rare = [exceptional_populations(anchor) for anchor in extra]
    per_profile = one_block_residual_bound()
    ones = [uniform_intersection(128, 8, 8, 17, r) for r in (0, 64)]
    require((rare, per_profile, ones) == ([87840, 87952], 85, [146, 106]), 'mixed count')
    mixed = sum(8*(n+2*4*per_profile) for n in ones)
    for prime, gain, slots, expected in (
            (PRIMES[0], 1935832, 39, (1079356632, 301560, 71642, 1078794742, 920811049)),
            (PRIMES[1], 920700, 82, (2160447288, 1130126, 143146, 2158985328, 921826181))):
        selected = sorted((q for row in rows for q in row[:h//gain]), reverse=True)[:slots]
        palettes = {a: {(v, e) for _, v, e, k in selected if a == k} for a in anchors}
        require(all(len(row)*gain <= h for row in palettes.values()) and
                slots*gain+h-1 <= len(anchors)*h, 'ten-fiber capacities')
        require(all(sum(v) in (32, 36, 40) for a in regular for v, _ in palettes[a])
                and all(sum(v) in (32, 62, 64) for a in extra for v, _ in palettes[a]),
                'selected weight classes')
        first_pairs = sum(overlaps(binary, order, 8, size, 8, [palettes[a] for a in regular]).values())
        extra_pairs = sum(overlaps(binary, order, 2, size, 0, [palettes[a] for a in extra]).values())
        total = sum(weight for weight, *_ in selected)
        words = total-sum(rare)-first_pairs-extra_pairs-mixed
        errors = LENGTH - (18*h-1+gain)
        require((total, first_pairs, extra_pairs, words, errors) == expected, 'ten-anchor certificate')
        require(words > prime//2**128, 'strict ten-anchor budget')
        print(f'Ten anchors, budget {prime//2**128}: {total} incidences, at least {words} '
              f'distinct words within {errors} errors.')


if __name__ == '__main__':
    small_control()
    for prime in PRIMES:
        check_signed_factors(prime, 128)
    with TemporaryDirectory() as temp:
        binary = Path(temp) / 'overlaps'
        run(['c++', '-O3', '-std=c++20', str(SOURCE), '-o', str(binary)], check=True)
        production(binary)
        ten_anchors(binary)
