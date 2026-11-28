#!/usr/bin/env python3
"""Certify a first-prime eighth-rate over-budget list with antipodal backups."""

from collections import defaultdict
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from probe_oriented_fiber_lists import oriented_counter, signature_pool
from probe_quarter_coset_lists import require
from probe_reciprocal_fiber_lists import signature_of
from probe_rotated_locator_union import (
    LENGTH, PRIMES, SOURCE, check_signed_factors, overlaps, relative_mode,
)


def opposite_signatures(order, step, size):
    """Return exact signed antipodal histograms conditional on a signless input."""
    width = size.bit_length()

    def encode(entries):
        return sum(value << (width * i) for i, value in enumerate(entries))

    # At an antipodal anchor the unordered pair ±node becomes ±(order/2-node).
    costs = {node: encode(signature_of({order // 2 - node}, order))
             for node in range(1, order // 2)}

    bits = 2 * order * order
    mask = (1 << bits) - 1

    def cyclic(value):
        folded = (value & mask) + (value >> bits)
        return (folded & mask) + (folded >> bits)

    def rotate(value, exponent):
        return cyclic(value << (order * exponent))

    def orient(value, node, occupancy):
        if occupancy == 0:
            return value
        if occupancy == 2:
            return rotate(value, order)
        return rotate(value, order // 2 - node) + rotate(value, order // 2 + node)

    @lru_cache(None)
    def subtree(node, signature):
        capacity = 0 if node % step == 0 else 2
        if len(signature) == 1:
            q = signature[0]
            return {q: {q * costs[node]: orient(1, node, q)}} if q <= min(capacity, size) else {}
        half = len(signature) // 2
        out = defaultdict(dict)
        for q in range(1 + min(capacity, min(signature), size)):
            remaining = tuple(x - q for x in signature)
            left = subtree(node // 2, remaining[:half])
            right = subtree((order - node) // 2, remaining[half:])
            for i, lhs in left.items():
                for j, rhs in right.items():
                    total = q + i + j
                    if total > size:
                        continue
                    aggregate = out[total]
                    for x, left_hist in lhs.items():
                        for y, right_hist in rhs.items():
                            key = q * costs[node] + x + y
                            joint = cyclic(left_hist * right_hist)
                            aggregate[key] = aggregate.get(key, 0) + orient(joint, node, q)
        return out

    def enumerate_at(signature):
        return subtree(order // 4, tuple(signature)).get(size, {})

    return encode, enumerate_at


def small_controls():
    for order, step, size in [(16, 4, 3), (32, 8, 5)]:
        encode, count = opposite_signatures(order, step, size)
        expected = defaultdict(dict)
        for roots in combinations([j for j in range(order) if j % step], size):
            original, _ = relative_mode(roots, 0, order)
            opposite, exponent = relative_mode(roots, order // 2, order)
            key = encode(opposite)
            expected[original][key] = expected[original].get(key, 0) + (1 << (order * exponent))
        for sig, actual in expected.items():
            require(count(sig) == actual, 'signed opposite counts disagree with explicit subsets')
        print(f'Order {order}: verified all {len(expected)} attainable input signatures.')


def main():
    small_controls()
    order, reserved, size, root = 128, 8, 17, 8
    step, h = order // reserved, LENGTH // order
    check_signed_factors(PRIMES[0], order)
    pool = signature_pool(order // 4, range(1, 4), 2, size, 500)
    count = oriented_counter(order, size, range(0, order, step))
    histograms = {tuple(v): count(v) for _, v in pool}
    slots = []
    for a in range(reserved):
        residue = (root - size * a * step) % order
        local = sorted(((hist[e], v, e, a) for v, hist in histograms.items()
                        for e in (residue, residue + order) if hist[e]), reverse=True)
        slots.extend(local[:5])
    selected = sorted(slots, reverse=True)[:34]
    anchors = [set() for _ in range(reserved)]
    for _, v, e, a in selected:
        anchors[a].add((v, e))
    full = [a for a in range(reserved) if len(anchors[a]) == 5]
    uniform = (1,) * (order // 4)
    require(full == [2, 7] and all(len(anchors[a]) in (4, 5) for a in range(reserved)),
            'primary palette shapes')
    for a in full:
        require(sum(v == uniform for v, _ in anchors[a]) == 2, 'two primary signs')
    _, get_support = opposite_signatures(order, step, size)
    support = get_support(uniform)
    signed = 2 * len(support)
    require(signed == 34136, 'opposite signature census')
    gain, backup = 1677731, 24
    used = [len(row) * gain for row in anchors]
    for a in full:
        used[a] -= 2 * backup
        used[(a + reserved // 2) % reserved] += signed * backup
    require(max(used) <= h and sum(used) + h - 1 <= reserved * h, 'fiber allotments')
    with TemporaryDirectory() as temp:
        binary = Path(temp) / 'overlaps'
        run(['c++', '-O3', '-std=c++20', str(SOURCE), '-o', str(binary)], check=True)
        pair_count = sum(overlaps(binary, order, reserved, size, root, anchors).values())
    incidences = sum(val for val, *_ in selected)
    words = incidences - pair_count
    radius = LENGTH - ((size + 1) * h - 1 + gain)
    require((incidences, pair_count, words, radius) ==
            (1092217628, 310704, 1091906924, 921069150), 'production certificate')
    require(words > PRIMES[0] // 2**128, 'strict designated budget')
    print(f'Full palette: {signed} opposite signed modes, {backup} backup sites per mode, '
          f'{reserved*h - sum(used) - (h-1)} spare beyond common roots. '
          f'At least {words} words at {radius} errors.')

    gain, backup, retained = 1677734, 31, 27055
    used = [len(row) * gain for row in anchors]
    lost = 0
    digit = (1 << order) - 1
    for a in full:
        opposite = (a + reserved // 2) % reserved
        residue = (root - size * opposite * step) % order
        weights = sorted(((hist >> (order * e)) & digit for hist in support.values()
                          for e in (residue, residue + order)), reverse=True)
        require(sum(weights) == sum(w for w, v, _, k in selected if k == a and v == uniform),
                'total mass of both primary signs')
        lost += sum(weights[retained:])
        used[a] -= 2 * backup
        used[opposite] += retained * backup
    require(max(used) <= h and sum(used) + h - 1 <= reserved * h, 'restricted allotments')
    radius = LENGTH - ((size + 1) * h - 1 + gain)
    require((lost, words - lost, radius) == (14127520, 1077779404, 921069147),
            'restricted production certificate')
    require(words - lost > PRIMES[0] // 2**128, 'restricted list above budget')
    print(f'Restricted palette: at most {lost} lost incidences, '
          f'{reserved*h - sum(used) - (h-1)} spare beyond common roots. '
          f'At least {words-lost} words at {radius} errors.')


if __name__ == '__main__':
    main()
