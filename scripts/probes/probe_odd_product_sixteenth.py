#!/usr/bin/env python3
"""Verify affine transports and odd-product list counts on the two named fields."""

import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
from subprocess import check_output, run
from tempfile import TemporaryDirectory

from check_sixteenth_locator_union import packed, write_pool
from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_reciprocal_fiber_lists import signature_of
from probe_rotated_locator_union import LENGTH, PRIMES, check_signed_factors

SOURCE = Path(__file__).with_suffix('.cpp')
PREFIX_TOTALS = {
    491520: (1059223840, 808980628),
    524288: (1114832816, 846069268),
    561737: (1177398496, 887336332),
    604947: (1248303696, 933304804),
    655360: (1329541376, 985235104),
    714938: (1423662416, 1044532172),
    745182: (1470709232, 1073740948),
    745183: (1470710784, 1073741956),
    786432: (1534202256, 1112969704),
    1310720: (2283324080, 1546525864),
    1572864: (2627858896, 1733268568),
    2200000: (3393490112, 2128536104),
}


def census(program, pool, m, degree, reserve, workers, caps):
    args = [str(x) for x in (pool, m, degree, reserve, workers, *caps)]
    rows = [tuple(map(int, s.split())) for s in check_output([program, *args], text=True).splitlines()]
    require([row[0] for row in rows] == sorted(caps), 'missing census prefix')
    return ({cap: (incidences, distinct) for cap, incidences, distinct, _ in rows},
            {cap: best for cap, _, _, best in rows})


def small_control(program, directory, m, degree, reserve, caps, workers):
    step = m//reserve
    pool = directory / f'control-{m}.pool'
    write_pool(pool, m, reserve, degree, 0, parity=1)
    roots = [t for t in combinations((j for j in range(m) if j % step), degree) if sum(t) % m == 1]
    inverse = {((1-u)*pow(degree, -1, m)) % m: pow(u, -1, m) for u in range(1, m, step)}

    def label(t, anchor):
        relative = {(inverse[anchor]*(x-anchor)) % m for x in t}
        require(sum(relative) % m == 1, 'transported product')
        return packed(signature_of(relative, m)), (sum(relative)//m) % 2

    labels = {a: [label(t, a) for t in roots] for a in range(0, m, step)}
    counts = Counter(labels[0])
    ranked = sorted(counts, key=lambda v: (-counts[v], v))
    actual, disjoint = census(program, pool, m, degree, reserve, workers, caps)
    ranks = {key: r for r, key in enumerate(ranked[:max(caps)])}
    owners = Counter()
    for i in range(len(roots)):
        hits = [ranks[row[i]] for row in labels.values() if row[i] in ranks]
        if hits:
            owners[min(hits)] += 1
    ordered = sorted(owners.values(), reverse=True)
    for cap in caps:
        selected = set(ranked[:cap])
        represented = {i for row in labels.values() for i, v in enumerate(row) if v in selected}
        count = sum(v in selected for row in labels.values() for v in row)
        require(actual[cap] == (count, len(represented)), 'exhaustive affine-board check')
        require(disjoint[cap] == sum(ordered[:cap]), 'direct minimum-rank population')
        if m == 16 and cap == 3:
            polynomial_control(m, degree, roots, labels, selected, represented)
    print(f'Order {m}: all {len(roots)} eligible root sets checked at {len(caps)} cutoffs.')


def polynomial_control(m, degree, roots, labels, selected, represented):
    prime, length, generator = 257, 128, 9
    h, gain = length//m, 2
    xs = [pow(generator, j, prime) for j in range(length)]
    ys = [pow(generator, h*j, prime) for j in range(m)]
    require(len(set(xs)) == length and pow(generator, length, prime) == 1, 'control grid')
    locators = [fiber_polynomial([ys[j] for j in t], prime) for t in roots]
    c = (-ys[1]) % prime
    assigned, spare = {}, []
    for a, row in labels.items():
        fiber = [x for x in xs if pow(x, h, prime) == ys[a]]
        for k, key in enumerate(sorted(selected)):
            values = {evaluate(locators[i], ys[a], prime) for i, val in enumerate(row) if val == key}
            require(len(values) == 1, 'one physical locator symbol per transported mode')
            for x in fiber[k*gain:(k+1)*gain]:
                assigned[x] = next(iter(values))
        spare.extend(fiber[len(selected)*gain:])
    require(len(spare) >= h-1, 'control common roots')
    common = fiber_polynomial(spare[:h-1], prime)
    center = []
    for x in xs:
        y = pow(x, h, prime)
        center.append(evaluate(common, x, prime)*(pow(y, degree, prime)+c-assigned.get(x, 0))*
                      pow(y, -1, prime) % prime)
    words = set()
    for index in represented:
        locator = locators[index]
        require(locator[0] == c, 'control locator constant')
        lifted = [0]*((degree-2)*h+1)
        lifted[::h] = [(-coefficient) % prime for coefficient in locator[1:-1]]
        polynomial = poly_mul(common, lifted, prime)
        require(len(polynomial) <= (degree-1)*h, 'control code degree')
        word = tuple(evaluate(polynomial, x, prime) for x in xs)
        require(sum(x == y for x, y in zip(word, center, strict=True)) >= (degree+1)*h-1+gain,
                'control physical agreements')
        words.add(word)
    require(len(words) == len(represented), 'distinct control codewords')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=(1, 2, 3), default=2)
    parser.add_argument('--controls-only', action='store_true')
    args = parser.parse_args()
    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        binary = directory/'census'
        run(['c++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Werror', '-pthread',
             str(SOURCE), '-o', str(binary)], check=True)
        small_control(binary, directory, 16, 3, 4, (1, 3, 8), args.workers)
        small_control(binary, directory, 32, 5, 8, (3, 15, 150), args.workers)
        if args.controls_only:
            return
        order, degree, reserve = 128, 9, 16
        h = LENGTH//order
        for prime in PRIMES:
            check_signed_factors(prime, order)
        pool = directory/'production.pool'
        write_pool(pool, order, reserve, degree, 6500, parity=1)
        require(pool.stat().st_size == 20*2958592, 'odd dictionary size')
        gains = (5, 6, 10, 11, 12, 13, 14, 15, 16)
        caps = [(15*h+1)//(16*g) for g in gains]
        counts, disjoint = census(binary, pool, order, degree, reserve, args.workers,
                                  caps + [745182, 745183, 2200000])
        require(disjoint[714938] == 1084262272 and disjoint[655360] == 1021595368,
                'first-budget reweighted disjoint populations')
        require(counts == PREFIX_TOTALS, 'production union or incidence counts')
        require(counts[745182][1] <= 2**30 < counts[745183][1], 'first-budget prefix crossing')
        require(2**31 - counts[2200000][1] == 18947544, 'second-field dictionary shortfall')
        for gain, cap in zip(gains, caps, strict=True):
            require(cap*gain <= h and reserve*cap*gain+h-1 <= reserve*h, 'physical capacity')
            incidences, distinct = counts[cap]
            print(f'Gain {gain}: {incidences} incidences, {distinct} words at {LENGTH-10*h+1-gain} errors.')
        print(f'Gain 11 with reassignment: at least {disjoint[714938]} words.')
        print(f'All 2,200,000 modes: {counts[2200000][1]} distinct words.')


if __name__ == '__main__':
    main()
