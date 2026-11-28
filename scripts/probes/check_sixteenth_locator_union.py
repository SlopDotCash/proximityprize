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
from math import prod
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


def write_pool(path, order, spare, degree, minimum, parity=0):
    """Emit signatures of the specified parity exceeding the unconditioned score threshold."""
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
                if weight % 2 != parity or len(polynomial) <= degree or polynomial[degree] <= minimum:
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


def census(program, pool, order, degree, spare, cut_a, cut_b, cap, workers, option=None):
    args = (pool, order, degree, spare, cut_a, cut_b, cap, workers)
    command = [program, option] if option else [program]
    result = subprocess.check_output([*command, *map(str, args)], text=True)
    rows = [tuple(map(int, match)) for match in re.findall(
        r'^bins=(\d+) incidences=(\d+) unique=(\d+)$', result, re.MULTILINE)]
    expected = sum(bool(n) for n in (cut_a, cut_b)) if option == '--signed-scores' else 2
    require(len(rows) == expected, 'one census row per active allocation')
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


def direct_product_scores(fixed, order, spare, cap, signed=False, bound_sites=None):
    """Rerank complete root sets by product and their unshared agreements at other anchors."""
    step = order // spare
    anchors = range(step, order, step)
    prime = 65537
    root = pow(3, (prime-1)//order, prime)
    values = {}

    def mode(relative):
        v = packed(signature_of(set(relative), order))
        return (v, (sum(relative)//order) % 2) if signed else v

    signatures = []
    for sites in fixed:
        row = {}
        for a in anchors:
            relative = [(j-a) % order for j in sites]
            row[a] = mode(relative)
            if signed:
                value = prod(1-pow(root, j, prime) for j in relative) % prime
                require(values.setdefault((a, row[a]), value) == value,
                        'each signed mode has one actual finite-field locator value')
        signatures.append(row)
    support = {a: defaultdict(set) for a in anchors}
    orbits = {}
    for i, row in enumerate(signatures):
        for a, v in row.items():
            support[a][v].add(i)
            if a & (a-1) or (a, v) in orbits:
                continue
            relative = [(j-a) % order for j in fixed[i]]
            image = {(u*a % order, mode([r*u % order for r in relative]))
                     for u in range(1, order, 2)}
            for b, other in image:
                if b == a:
                    orbits[a, other] = image

    def choose(current, target=0):
        selected = {entry for entry in current if target and entry[0] & -entry[0] != target}
        for a in anchors:
            if a & (a-1) or (target and a != target):
                continue
            ranked = []
            seen = set()
            for v, members in support[a].items():
                if v in seen:
                    continue
                orbit = orbits[a, v]
                local = {w for b, w in orbit if b == a}
                seen.update(local)
                fresh = sum(not any((b, signatures[i][b]) in current for b in anchors if b != a)
                            for i in members)
                score = fresh if target else len(members)+(2 if signed else 3)*fresh
                if score:
                    ranked.append((-score, min(local), len(local), orbit))
            used = 0
            for _, _, size, orbit in sorted(ranked):
                if used + size <= cap:
                    selected.update(orbit)
                    used += size
        return selected

    initial = choose(set())
    if bound_sites is not None:
        hits = [sum(item in initial for item in row.items()) for row in signatures]
        repeated = {i for i, count in enumerate(hits) if count >= 2}
        panel, incidence = {}, 0
        for a in anchors:
            sizes = sorted((len(members-repeated) for members in support[a].values()), reverse=True)
            full, next_mode = sum(sizes[:cap]), sizes[cap] if len(sizes) > cap else 0
            incidence += 5*full+(bound_sites%5)*next_mode
            if not a & (a-1):
                panel[a] = (full, next_mode if bound_sites%5 else 0)
        return panel, (sum(n == 1 for n in hits), len(repeated), len(repeated)+incidence//5)
    selected = choose(initial)
    if signed:
        selected = choose(choose(selected, order//2), order//4)
    counts = [sum(item in selected for item in row.items()) for row in signatures]
    bins = max(sum((a, v) in selected for v in support[a]) for a in anchors)
    baseline = (bins, sum(counts), sum(count > 0 for count in counts))
    if not signed:
        return baseline
    a = order//4
    unchanged = {item for item in selected if item[0] != a}
    covered = {i for i, row in enumerate(signatures) if any(item in unchanged for item in row.items())}
    ranked = sorted(support[a], key=lambda v: (-len(support[a][v]-covered), v))
    final = set(covered)
    for v in ranked[:cap]:
        final.update(support[a][v])
    return baseline, baseline[2]-len(covered), len(final)-len(covered)


def gain_five_cap(program, pool, order, degree, spare, sites, workers):
    arguments = [str(x) for x in (pool, order, degree, spare, sites, workers)]
    output = subprocess.check_output([program, '--gain-five-cap', *arguments], text=True)
    panel = {int(a): (int(full), int(tail)) for a, full, tail in re.findall(
        r'^anchor=(\d+) full=(\d+) next=(\d+)$', output, re.MULTILINE)}
    totals = re.search(r'^single=(\d+) repeated=(\d+) upper=(\d+)$', output, re.MULTILINE)
    require(totals is not None, 'gain-five cap totals')
    return panel, tuple(map(int, totals.groups()))


def small_board(program, directory, order, spare, degree, workers, check_cap=False):
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
    fixed = [t for t in all_sites if sum(t) % order == 0]
    caps = (1, 3) if order == 16 else (35, 100)
    refined = [direct_product_scores(fixed, order, spare, cap) for cap in caps]
    computed, _ = census(program, pool, order, degree, spare, *caps, 1, workers, option="--product-scores")
    require(computed == refined, 'independent product and unshared-population ranking')
    print(f'M={order} refined={computed}')
    signed_cap = 3 if order == 16 else 70
    baseline, previous, offered = direct_product_scores(fixed, order, spare, signed_cap, signed=True)
    signed_rows, output = census(program, pool, order, degree, spare, signed_cap, 0, 3, workers,
                                 option="--signed-scores")
    require(signed_rows == [baseline] and
            f'response_anchor={order//4} pool=0 previous={previous} offered={offered} '
            f'increase={offered-previous}' in output, 'direct signed union and single anchor replacement')
    print(f'M={order} signed={baseline} final={baseline[2]+offered-previous}')
    if check_cap:
        sites = 5*signed_cap+3
        expected = direct_product_scores(fixed, order, spare, signed_cap, signed=True, bound_sites=sites)
        actual = gain_five_cap(program, pool, order, degree, spare, sites, workers)
        require(actual == expected, 'direct residual modal capacities and gain-five upper bound')
        print(f'M={order} gain-five cap={actual[1]}')
    if order == 16:
        explicit_words(order, spare, degree, selected[1], len(b_pool))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=(1,2,3), default=2)
    parser.add_argument('--controls-only', action='store_true')
    parser.add_argument('--gain-five-cap', action='store_true',
                        help='verify the allocation upper bound on the product-one signed dictionary')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        program = directory/'union'
        source = Path(__file__).with_name('probe_sixteenth_locator_union.cpp')
        subprocess.run([os.environ.get('CXX','c++'), '-std=c++17', '-Wall', '-Wextra', '-Werror',
                        '-O3', str(source), '-o', str(program)], check=True)
        small_board(program, directory, 16, 4, 3, args.workers, args.gain_five_cap)
        small_board(program, directory, 32, 8, 5, args.workers, args.gain_five_cap)
        if args.controls_only:
            return
        pool = directory/'production.pool'
        write_pool(pool, 128, 16, 9, 7680)
        require(pool.stat().st_size == 20*1923274, 'complete production pool size')
        h, n = 2**23, 2**30
        if args.gain_five_cap:
            panel, totals = gain_five_cap(program, pool, 128, 9, 16, h, args.workers)
            require(panel == {8: (111800157,59), 16: (111398538,58),
                              32: (111168866,58), 64: (125988044,60)} and
                    totals == (1422335424,364739488,2053061200), 'gain-five allocation upper bound')
            print(f'anchors={panel} single={totals[0]} repeated={totals[1]} upper={totals[2]}')
            return
        rows, output = census(program, pool, 128, 9, 16, 9504, 8192, h//6, args.workers)
        print('Uniform pools')
        print(output, end='')
        require(rows == [(517954,1551671296,1132216224),(1398090,3367652416,2459641984)],
                'production receipts')
        rows, output = census(program, pool, 128, 9, 16, h//20, h//8, 1, args.workers,
                              option="--product-scores")
        print('Product-conditioned pools after one overlap refinement')
        print(output, end='')
        require(rows == [(419430,1276465776,1124276896),(1048576,2659659888,2183380672)],
                'product-conditioned production receipts')
        for (bins, _, size), budget in zip(rows, (n, 2*n)):
            gain = h//(2*bins)
            require(size > budget, 'over-budget list')
            print(f'budget={budget} list={size} gain={gain} first_bad<={n-10*h+1-gain}')
        cap = h//11
        signed_rows, output = census(program, pool, 128, 9, 16, cap, 0, 3, args.workers,
                                     option="--signed-scores")
        print('Signed modes at the first budget')
        print(output, end='')
        require(signed_rows == [(762600,1240417392,1073709616)] and
                'response_anchor=32 pool=0 previous=61386048 offered=63078124 increase=1692076'
                in output, 'signed census and one-anchor substitution')
        size = signed_rows[0][2] - 61386048 + 63078124
        require(size == 1075401692 and size > n and cap*11 <= h, 'over-budget signed witness')
        print(f'budget={n} list={size} gain=11 first_bad<={n-10*h+1-11}')


if __name__ == '__main__':
    main()
