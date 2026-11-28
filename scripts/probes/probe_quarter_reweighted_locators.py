#!/usr/bin/env python3
"""Verify two quarter-rate list witnesses selected with pair-overlap penalties."""

from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from probe_oriented_fiber_lists import oriented_counter, signature_pool
from probe_quarter_coset_lists import require
from probe_rotated_locator_union import LENGTH, PRIMES, SOURCE, check_signed_factors, overlaps

# All indices below the prefix are selected. Bit j selects rank prefix+j.
# The most significant hexadecimal digit appears first, as for int(text, 16).
CASES = (
    (12, 1680,
     'ff000000ffffffffff00ffffffffff00000000ffff000000ff000000ff00000000ff000000000000ffff'
     'ffffff0000ffffffff00ff00ffffffffff00000000ffffffffffff00000000ffff0000ffffffffffff07'
     'feffffffff0000ffffffffffffffffffff0000',
     (2162, 1088872068, 14893542, 1073978526, 23280, 771728657)),
    (15, 4284,
     '2a66a0aa06565aa60a9aaa6969699a6aa66656a966a9aaa6a0a06660a9a0950060a69a6a0a0aa8e9a0aa'
     'aa600af09a9af95a555fff556fff5595f659569599656f695555f99599ffaff595555555f95a9fa965f9'
     '659af9959665f9ddff5f555996f9999ffaf959fff6ff55555ffff6',
     (4769, 2166222587, 18582533, 2147640054, 10553, 771741384)),
)


def production(binary):
    size, order, h = 17, 64, LENGTH//64
    count = oriented_counter(order, size, range(0, order, 16))
    pool = signature_pool(16, range(1, 6), 3, size, 12000)
    histograms = {tuple(v): count(v) for _, v in pool}
    for prime, (product, prefix, bits, expected) in zip(PRIMES, CASES, strict=True):
        check_signed_factors(prime, order)
        candidates = []
        for anchor in range(4):
            residue = (product-17*16*anchor) % order
            candidates += [(row[e], v, e, anchor) for v, row in histograms.items()
                           for e in (residue, residue+order) if row[e]]
        candidates.sort(reverse=True)
        mask = int(bits, 16)
        selected = candidates[:prefix] + [candidates[prefix+j] for j in range(mask.bit_length())
                                          if (mask >> j) & 1]
        palettes = [set() for _ in range(4)]
        for _, v, e, a in selected:
            palettes[a].add((v, e))
        k = len(selected)
        gain = (3*h+1)//k
        require(all(len(row)*gain <= h for row in palettes) and k*gain+h-1 <= 4*h,
                'physical fiber capacities')
        singles = sum(w for w, *_ in selected)
        pairs = sum(overlaps(binary, order, 4, size, product, palettes).values())
        distinct = singles-pairs
        errors = LENGTH-18*h+1-gain
        require((k, singles, pairs, distinct, gain, errors) == expected and
                distinct > prime//2**128, 'strict over-budget witness')
        print(f'{k} modes, {singles} incidences, {pairs} pair intersections. '
              f'At least {distinct} words at {errors} errors.')


if __name__ == '__main__':
    with TemporaryDirectory() as temp:
        exe = Path(temp) / 'pair-counter'
        run(['c++', '-std=c++20', '-O3', str(SOURCE), '-o', str(exe)], check=True)
        production(exe)
