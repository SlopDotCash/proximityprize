"""Check the two rate-1/16 witnesses with direct controls and an exact quotient census.

Run python3 scripts/probes/check_sixteenth_locator_union.py --workers 3.
The default runs both controls and the production computation in a temporary directory.
"""
import argparse
import os
import re
import struct
import subprocess
import tempfile
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path

from probe_multifiber_sixteenth_lists import shapes
from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_reciprocal_fiber_lists import counts, signature_of


def packed(entries):
    return sum(value << (4*i) for i, value in enumerate(entries))


@lru_cache(None)
def orientations(v):
    """All distinct labelled versions of a canonical vector of leaf entries."""
    if len(v) == 1:
        return (v,)
    middle = len(v) // 2
    children = product(orientations(v[:middle]), orientations(v[middle:]))
    return tuple({ordered for left, right in children for ordered in (left+right, right+left)})


def multiset_orders(keys):
    if not keys:
        yield ()
        return
    for i, value in enumerate(keys):
        if i and value == keys[i-1]:
            continue
        for tail in multiset_orders(keys[:i] + keys[i+1:]):
            yield (value,) + tail


def write_pool(path, order, spare, degree, minimum):
    """Emit all even signatures with strictly more than minimum unconditioned root sets."""
    leaves = order // (2 * spare)
    trees = spare // 2
    local = set().union(*(shapes(leaves.bit_length()-1, d) for d in range(degree+1)))
    options = sorted((next(i for i, n in enumerate(counts(v)) if n), v) for v in local)
    oriented = {v: tuple(map(packed, orientations(v))) for _, v in options}
    poly = {v: counts(v)[:degree+1] for _, v in options}

    @lru_cache(None)
    def multiply(a, b):
        return tuple(sum(x*b[i-j] for j, x in enumerate(a) if 0 <= i-j < len(b))
                     for i in range(min(degree+1, len(a)+len(b)-1)))

    with path.open('wb') as out:
        # For the production board each subtree occupies exactly one uint16.
        record = struct.Struct('<8HI') if leaves == 4 and trees == 8 else None

        def visit(start, remaining, chosen, polynomial, weight):
            if len(chosen) == trees:
                if weight % 2 or len(polynomial) <= degree or polynomial[degree] <= minimum:
                    return
                score = polynomial[degree]
                for order_of_trees in multiset_orders(chosen):
                    for labels in product(*(oriented[x] for x in order_of_trees)):
                        if record:
                            out.write(record.pack(*labels, score))
                        else:
                            value = sum(v << (4*leaves*i) for i, v in enumerate(labels))
                            out.write(value.to_bytes(16, 'little') + score.to_bytes(4, 'little'))
                return
            for j in range(start, len(options)):
                cost, v = options[j]
                if cost * (trees-len(chosen)) > remaining:
                    break
                visit(j, remaining-cost, chosen+(v,), multiply(polynomial, poly[v]), weight+sum(v))

        visit(0, degree, (), (1,), 0)


def census(program, pool, order, degree, spare, cut_a, cut_b, cap, workers):
    args = (pool, order, degree, spare, cut_a, cut_b, cap, workers)
    result = subprocess.check_output([program, *map(str, args)], text=True)
    rows = [tuple(map(int, match)) for match in re.findall(
        r'^bins=(\d+) incidences=(\d+) unique=(\d+)$', result, re.MULTILINE)]
    require(len(rows) == 2, 'two census rows')
    return rows, result


def explicit_words(order, spare, degree, selected, pool_size):
    """Expand every codeword of the small list about one constructed finite-field center."""
    p, n = 65537, order*64
    h = n // order
    gain = h // (2*pool_size)
    require(gain > 0 and selected, 'positive agreement gain')
    g = pow(3, (p-1)//n, p)
    require(pow(g,n//2,p) == p-1, 'exact order')
    xs = [pow(g, i, p) for i in range(n)]
    ys = [pow(g, h*i, p) for i in range(order)]
    fibers = defaultdict(list)
    for x in xs:
        fibers[pow(x, h, p)].append(x)
    common = fiber_polynomial(fibers[1][1:], p)
    values = defaultdict(set)
    polynomials = []
    fixed = (-1)**degree % p
    for sites, anchors in selected:
        loc = fiber_polynomial([ys[i] for i in sites], p)
        require(loc[0] == fixed, 'prescribed root product')
        head = [-a % p for a in loc[1:-1]]
        for anchor in anchors:
            values[anchor].add(evaluate(head, ys[anchor], p))
        lift = [0]*((len(head)-1)*h+1)
        lift[::h] = head
        expanded = poly_mul(common, lift, p)
        require(len(expanded) <= (degree-1)*h, 'degree below code dimension')
        polynomials.append(expanded)
    assignments = {}
    step = order // spare
    for a, modes in values.items():
        require(a and a % step == 0 and len(modes) <= 2*pool_size, 'modes at a spare anchor')
        for i, mode in enumerate(sorted(modes)):
            for x in fibers[ys[a]][i*gain:(i+1)*gain]:
                assignments[x] = mode
    center = []
    for x in xs:
        y = pow(x,h,p)
        base = (pow(y, degree, p)+fixed)*pow(y,-1,p) % p
        center.append(evaluate(common,x,p)*assignments.get(x,base) % p)
    words = set()
    least_agreements = n
    for polynomial in polynomials:
        word = tuple(evaluate(polynomial, x, p) for x in xs)
        agreements = sum(a == b for a, b in zip(word, center))
        least_agreements = min(least_agreements, agreements)
        words.add(word)
    require(len(words) == len(selected) and least_agreements >= (degree+1)*h-1+gain,
            'distinct words in the claimed ball')
    print(f'F_{p} n={n} explicit_words={len(words)} min_agreements={least_agreements}')


def small_board(program, directory, order, spare, degree, workers):
    """Compute raw signatures, Galois orbits and anchored unions directly from root subsets."""
    pool = directory/'small.pool'
    write_pool(pool, order, spare, degree, 0)
    step = order // spare
    ordinary = [i for i in range(order) if i % step]
    all_sites = list(combinations(ordinary, degree))
    scores = Counter()
    representative = {}
    for t in all_sites:
        signature = signature_of(set(t), order)
        if sum(signature) % 2 == 0:
            key = packed(signature)
            scores[key] += 1
            representative[key] = t
    output = {lo+(hi << 64): score for lo, hi, score
              in struct.iter_unpack('<QQI', pool.read_bytes())}
    require(pool.stat().st_size == 20*len(scores) and output == scores, 'complete direct scores')
    levels = sorted(set(scores.values()))
    cut_a, cut_b = levels[len(levels)//2], levels[len(levels)//3]
    a_pool = {v for v in scores if scores[v] > cut_a}
    b_pool = {v for v in scores if scores[v] > cut_b}
    ties = sorted(v for v in scores if scores[v] == cut_b)
    cap = len(b_pool) + (len(ties)+1)//2
    seen = set()
    for v in ties:
        if v in seen:
            continue
        orbit = {packed(signature_of({u*j % order for j in representative[v]}, order))
                 for u in range(1, order, 2)}
        seen.update(orbit)
        if len(b_pool) + len(orbit) <= cap:
            b_pool.update(orbit)
    selected = [[], []]
    for t in all_sites:
        if sum(t) % order:
            continue
        signatures = {a: packed(signature_of({(j-a) % order for j in t}, order))
                      for a in range(step, order, step)}
        for pool_id, keys in enumerate([a_pool, b_pool]):
            anchors = [a for a, v in signatures.items() if v in keys]
            if anchors:
                selected[pool_id].append((t, anchors))
    expected = [(len(keys), sum(len(anchors) for _, anchors in coll), len(coll))
                for keys, coll in zip((a_pool, b_pool), selected)]
    actual, _ = census(program, pool, order, degree, spare, cut_a, cut_b, cap, workers)
    require(actual == expected and any(inc > count > 0 for _, inc, count in expected),
            'direct union and overlapping incidences')
    print(f'M={order} S={spare} degree={degree} subsets={len(all_sites)} direct={expected}')
    if order == 16:
        explicit_words(order, spare, degree, selected[1], len(b_pool))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=(1,2,3), default=2)
    parser.add_argument('--controls-only', action='store_true')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        program = directory/'union'
        source = Path(__file__).with_name('probe_sixteenth_locator_union.cpp')
        subprocess.run([os.environ.get('CXX','c++'), '-std=c++17', '-Wall', '-Wextra', '-Werror',
                        '-O3', str(source), '-o', str(program)], check=True)
        small_board(program, directory, 16, 4, 3, args.workers)
        small_board(program, directory, 32, 8, 5, args.workers)
        if args.controls_only:
            return
        pool = directory/'production.pool'
        write_pool(pool, 128, 16, 9, 7680)
        require(pool.stat().st_size == 20*1923274, 'complete production pool size')
        h, n = 2**23, 2**30
        rows, output = census(program, pool, 128, 9, 16, 9504, 8192, h//6, args.workers)
        print(output, end='')
        require(rows == [(517954,1551671296,1132216224),(1398090,3367652416,2459641984)],
                'production receipts')
        for (bins, _, size), budget in zip(rows, (n, 2*n)):
            gain = h//(2*bins)
            require(size > budget, 'over-budget list')
            print(f'budget={budget} list={size} gain={gain} first_bad<={n-10*h+1-gain}')


if __name__ == '__main__':
    main()
