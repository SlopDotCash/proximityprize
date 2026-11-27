#!/usr/bin/env python3
"""Verify the quarter- and eighth-rate list witnesses on both named primes."""

from collections import Counter
from itertools import combinations
from pathlib import Path
from subprocess import PIPE, run
from tempfile import TemporaryDirectory

from probe_oriented_fiber_lists import oriented_counter, signature_pool
from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_reciprocal_fiber_lists import signature_of

LENGTH = 2**30
PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)
SOURCE = Path(__file__).with_suffix(".cpp")


def overlaps(executable, order, reserved, size, root, palettes):
    request = [f"{order} {reserved} {size} {root}"]
    for a, palette in enumerate(palettes):
        for vector, exponent in palette:
            request.append(" ".join(map(str, (a, exponent, *vector))))
    output = run([executable], input="\n".join(request) + "\n", text=True, stdout=PIPE, check=True)
    rows = [tuple(map(int, line.split())) for line in output.stdout.splitlines()]
    result = {(a, b): count for a, b, count in rows}
    require(len(rows) == len(result) and set(result) == set(combinations(range(reserved), 2)),
            "incomplete pair census")
    return result


def relative_mode(roots, anchor, order):
    shifted = {(j - anchor) % order for j in roots}
    return signature_of(shifted, order), sum(shifted) % (2 * order)


def check_small_board(executable, order, reserved, size, *, expand=False):
    step = order // reserved
    ordinary = [j for j in range(order) if j % step]
    # A single product class suffices for the witness and for all pair comparisons.
    root = 1
    sets = [roots for roots in combinations(ordinary, size) if sum(roots) % order == root]
    modes = [[relative_mode(roots, a * step, order) for roots in sets] for a in range(reserved)]
    for scheme in range(3):
        palettes = []
        for a, row in enumerate(modes):
            freq = Counter(row)
            ranked = sorted(freq, key=lambda key: (freq[key], key), reverse=True)
            if scheme == 0:
                selected = ranked
            elif scheme == 1:
                selected = ranked[(a % 3)::3]
            else:
                selected = ranked[:2]
            palettes.append(set(selected))
        represented = [{i for i, key in enumerate(row) if key in palette}
                       for row, palette in zip(modes, palettes, strict=True)]
        actual = {(a, b): len(represented[a] & represented[b]) for a, b in combinations(range(reserved), 2)}
        require(overlaps(executable, order, reserved, size, root, palettes) == actual,
                "cycle count disagrees with explicit subsets")
        if expand and scheme == 2:
            check_polynomials(order, reserved, size, root, sets, modes, palettes, represented)
    print(f"Order {order}, {reserved} anchors: checked three full pair censuses on {len(sets)} root sets.")


def check_polynomials(order, reserved, size, root, sets, modes, palettes, represented):
    p, n, generator = 257, 128, 9
    h, step = n // order, order // reserved
    xs = [pow(generator, j, p) for j in range(n)]
    ys = [pow(generator, h * j, p) for j in range(order)]
    require(len(set(xs)) == n and pow(generator, n, p) == 1, "field-control generator")
    locators = [fiber_polynomial([ys[j] for j in roots], p) for roots in sets]
    fixed = ((-1)**size * ys[root]) % p
    require(all(loc[0] == fixed for loc in locators), "constant term")
    gain = min(h // max(map(len, palettes)), ((reserved - 1) * h + 1) // sum(map(len, palettes)))
    require(gain > 0, "positive gain")
    allocated, spare = {}, []
    for a, palette in enumerate(palettes):
        y = ys[a * step]
        sites = [x for x in xs if pow(x, h, p) == y]
        for index, key in enumerate(sorted(palette)):
            symbols = {evaluate(locator, y, p) for locator, mode in zip(locators, modes[a], strict=True)
                       if mode == key}
            require(len(symbols) == 1, "one actual value per signed mode")
            for x in sites[index*gain:(index+1)*gain]:
                allocated[x] = next(iter(symbols))
        spare.extend(sites[len(palette)*gain:])
    common = fiber_polynomial(spare[:h-1], p)
    require(len(common) == h, "room for the common roots")
    center = []
    for x in xs:
        y = pow(x, h, p)
        center.append(evaluate(common, x, p) * (pow(y, size, p) + fixed - allocated.get(x, 0))
                      * pow(y, -1, p) % p)
    selected = set.union(*represented)
    words = set()
    for i in selected:
        lifted = [0] * ((size - 2) * h + 1)
        lifted[::h] = [(-c) % p for c in locators[i][1:-1]]
        polynomial = poly_mul(common, lifted, p)
        require(len(polynomial) <= (size-1)*h, "Reed--Solomon degree")
        word = tuple(evaluate(polynomial, x, p) for x in xs)
        require(sum(x == y for x, y in zip(word, center, strict=True)) >= (size+1)*h-1+gain,
                "insufficient actual agreements")
        words.add(word)
    require(len(words) == len(selected), "word collision")
    print(f"Prime {p}, length {n}: verified {len(words)} distinct words at all {n} sites.")


def check_signed_factors(prime, order):
    # The sine doubling identities used in the norm tree are identities of roots of unity.
    # Checking each single-root factor proves the formula for every subset by multiplication.
    halfroot = next(pow(a, (prime-1)//(2*order), prime) for a in range(2, 1000)
                    if pow(a, (prime-1)//2, prime) == prime-1)
    require(pow(halfroot, order, prime) == prime-1, "primitive root")
    unit = halfroot**2 % prime
    imaginary = pow(halfroot, order//2, prime)

    def leaves(j):
        return [j] if j % 2 else leaves(j//2) + leaves((order-j)//2)
    weights = [imaginary * (pow(halfroot, -j, prime) - pow(halfroot, j, prime)) % prime
               for j in leaves(order//4)]
    for j in range(1, order):
        if j == order//2:
            continue
        value = -imaginary * pow(halfroot, j, prime) % prime
        for base, power in zip(weights, signature_of({j}, order), strict=True):
            value = value * pow(base, power, prime) % prime
        require(value == (1 - pow(unit, j, prime)) % prime, "incorrect signed singleton")


def production(executable, order, reserved, pool_shape, cases):
    size = 17
    h = LENGTH // order
    step = order // reserved
    count = oriented_counter(order, size, range(0, order, step))
    levels, deviations, limit = pool_shape
    pool = signature_pool(order//4, levels, deviations, size, limit)
    histograms = {tuple(v): count(v) for _, v in pool}
    for prime, (root, gain, slot_limit, expected) in zip(PRIMES, cases, strict=True):
        check_signed_factors(prime, order)
        ranked = []
        for a in range(reserved):
            residue = (root - size*a*step) % order
            row = sorted(((hist[e], v, e, a) for v, hist in histograms.items()
                          for e in (residue, residue+order) if hist[e]), reverse=True)
            ranked.extend(row[:h//gain])
        selected = sorted(ranked, reverse=True)[:slot_limit]
        palettes = [set() for _ in range(reserved)]
        for _, v, e, a in selected:
            palettes[a].add((v, e))
        require(sum(map(len, palettes)) == slot_limit and
                slot_limit*gain + h-1 <= reserved*h and max(map(len, palettes))*gain <= h,
                "fiber capacities")
        single = sum(weight for weight, *_ in selected)
        repeated = sum(overlaps(executable, order, reserved, size, root, palettes).values())
        distinct = single - repeated
        errors = LENGTH - ((size+1)*h-1+gain)
        budget = prime // 2**128
        require((single, repeated, distinct, errors) == expected and distinct > budget,
                "production certificate")
        print(f"Rate 1/{order//16}, budget {budget}: {single} incidences, "
              f"{repeated} pair repetitions, at least {distinct} words at {errors} errors.", flush=True)


def main():
    with TemporaryDirectory() as temporary:
        executable = Path(temporary) / "rotated-locator-union"
        run(["c++", "-O3", "-std=c++20", str(SOURCE), "-o", str(executable)], check=True)
        check_small_board(executable, 8, 2, 3)
        check_small_board(executable, 16, 4, 5, expand=True)
        check_small_board(executable, 32, 8, 5)
        production(executable, 64, 4, (range(1, 6), 3, 9000), QUARTER)
        production(executable, 128, 8, (range(1, 4), 2, 500), EIGHTH)


# Each entry fixes a root-product exponent, agreements per selected mode, total modes,
# and the expected (single occurrences, pair intersections, union lower bound, errors).
QUARTER = (
    (12, 23269, 2163, (1090462734, 16704778, 1073757956, 771728668)),
    (15, 10549, 4771, (2167292585, 19647448, 2147645137, 771741388)),
)
EIGHTH = (
    (8, 1677721, 34, (1092217628, 310704, 1091906924, 921069160)),
    (8, 863533, 68, (2151345320, 1729758, 2149615562, 921883348)),
)


if __name__ == "__main__":
    main()
