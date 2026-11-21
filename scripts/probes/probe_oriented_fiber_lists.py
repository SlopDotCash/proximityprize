"""Certify larger Reed–Solomon lists on the two named length-2^30 domains.

A quotient root set T of size m has two labels: its reciprocal-tree signature
v from probe_reciprocal_fiber_lists.py and the sum r of its ordinary root
exponents (each in [1,M-1]), taken modulo 2M. Together these labels determine
the unsquared locator L_T(1) over either named field. To see this, take the
complex primitive M-th root zeta = exp(2*pi*i/M). Each factor 1-zeta^j equals
(-2i) exp(pi*i*j/M) sin(pi*j/M), with the sine positive. The norm-doubling
identity shows that v fixes the absolute value of the product, and r fixes its
phase. Equality in the cyclotomic integers specializes to any primitive M-th
root in an odd-characteristic field: the monic minimal polynomial is
X^(M/2)+1. Also r mod M fixes the root product and hence L_T(0).

For one fixed root product, select K disjoint labels with total population
above the security budget. All selected words have at most K locator values at
one, even if two labels specialize to the same value. With h = 2^30/M, the
reserved-fiber construction in docs/research/proximity-gap/reciprocal-fiber-lists.md
therefore gives (m+1)*h - 1 + floor(h/K) agreements per word. Its dimension
is (m-1)*h. Repeating a scalar row gives the same conclusion at every positive
interleaving width. The output bounds first failure from above.

Run with python3 scripts/probes/probe_oriented_fiber_lists.py.
"""

from functools import lru_cache
from itertools import combinations, product
from math import prod

from probe_reciprocal_fiber_lists import counts, signature_of


def require(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(None)
def canonical_signature(signature):
    """Child swaps preserve the ordinary, unoriented population polynomial."""
    if len(signature) == 1:
        return signature
    middle = len(signature) // 2
    left = canonical_signature(signature[:middle])
    right = canonical_signature(signature[middle:])
    return left + right if left <= right else right + left


def signature_pool(leaves, levels, deviations, subset_size, limit):
    """Perturb a constant signature on dyadic intervals of labelled leaves."""
    intervals = [(start, start + w) for w in (1, 2, 4, 8, 16) if w < leaves
                 for start in range(0, leaves, w)]
    candidates = set()
    for level in levels:
        for size in range(deviations + 1):
            for spans in combinations(intervals, size):
                for changes in product((-1, 1), repeat=size):
                    entries = [level] * leaves
                    for (start, stop), change in zip(spans, changes):
                        for i in range(start, stop):
                            entries[i] += change
                    if min(entries) >= 0:
                        candidates.add(bytes(entries))
    ranked = []
    for signature in candidates:
        distribution = counts(tuple(canonical_signature(signature)))
        if len(distribution) > subset_size and distribution[subset_size]:
            ranked.append((distribution[subset_size], signature))
    return sorted(ranked, reverse=True)[:limit]


def oriented_counter(order, subset_size):
    """Count (degree, exponent mod 2M) for each fixed labelled signature.

    Store a cyclic histogram as digits in base 2^M. Each digit counts subsets
    of at most M-2 roots, hence is below this base, including before cyclic
    reduction. Integer multiplication followed by end-around carry of whole
    histograms performs exact cyclic convolution without per-digit carries.
    """
    bits = order
    width = 2 * order * bits
    mask = (1 << width) - 1
    digit = (1 << bits) - 1

    def fold(value):
        reduced = (value >> width) + (value & mask)
        return (reduced >> width) + (reduced & mask)

    def rotate(value, exponent):
        return fold(value << (exponent * bits))

    @lru_cache(None)
    def subtree(node, signature):
        if len(signature) == 1:
            occupancy = signature[0]
            choices = (1, (1 << (bits * node)) + (1 << (bits * (order - node))),
                       1 << (bits * order))
            return {occupancy: choices[occupancy]} if occupancy <= 2 else {}
        middle = len(signature) // 2
        result = {}
        for occupancy in range(min(2, min(signature)) + 1):
            reduced = tuple(v - occupancy for v in signature)
            left = subtree(node // 2, reduced[:middle])
            right = subtree((order - node) // 2, reduced[middle:])
            joined = {}
            for i, first in left.items():
                for j, second in right.items():
                    size = i + j + occupancy
                    if size <= subset_size:
                        joined[size] = joined.get(size, 0) + fold(first * second)
            for size, labels in joined.items():
                if occupancy == 1:
                    labels = rotate(labels, node) + rotate(labels, order - node)
                elif occupancy == 2:
                    labels = rotate(labels, order)
                result[size] = result.get(size, 0) + labels
        return result

    def count(signature):
        encoded = subtree(order // 4, tuple(signature)).get(subset_size, 0)
        return [(encoded >> (r * bits)) & digit for r in range(2 * order)]

    return count


def small_check(order, subset_size, prime):
    root = next(u for u in range(2, prime)
                if pow(u, order, prime) == 1 and pow(u, order // 2, prime) != 1)
    actual = {}
    locators = {}
    for selected in combinations([j for j in range(1, order) if j != order // 2], subset_size):
        signature = signature_of(set(selected), order)
        exponent = sum(selected) % (2 * order)
        row = actual.setdefault(signature, [0] * (2 * order))
        row[exponent] += 1
        value = prod(1 - pow(root, j, prime) for j in selected) % prime
        key = (signature, exponent)
        require(locators.setdefault(key, value) == value, "locator label collision")
    count = oriented_counter(order, subset_size)
    for signature, histogram in actual.items():
        require(count(signature) == histogram, "small histogram")


def production(order, size, levels, deviations, limit, expected):
    n = 2**30
    h = n // order
    count = oriented_counter(order, size)
    rows = [[] for _ in range(order)]
    for population, signature in signature_pool(order // 4, levels, deviations, size, limit):
        histogram = count(signature)
        require(sum(histogram) == population, "oriented population total")
        for exponent, amount in enumerate(histogram):
            if amount:
                rows[exponent % order].append(amount)

    for field_index, budget in enumerate((n, 2*n), 1):
        offers = []
        for root_class, row in enumerate(rows):
            total = 0
            for bins, quantity in enumerate(sorted(row, reverse=True), 1):
                total += quantity
                if total > budget:
                    offers.append((bins, -total, root_class))
                    break
        require(offers, "no over-budget class")
        bins, negative_total, root_class = min(offers)
        gain = h // bins
        errors = n - (size + 1)*h + 1 - gain
        receipt = (bins, root_class, -negative_total, gain, errors)
        require(receipt == expected[field_index - 1], "production certificate changed")
        print(f"P{field_index} rate 1/{order // (size-1)}: bins={bins} root={root_class} "
              f"words={-negative_total} gain={gain} first_failure<={errors}")



def uniform_coincidences(order, size, level):
    """Count root products for which T and -T have the specified constant signature."""
    def combine(first, second):
        result = {}
        for (d, r), amount in first.items():
            for (e, s), other in second.items():
                if d + e <= size:
                    key = d + e, (r + s) % order
                    result[key] = result.get(key, 0) + amount * other
        return result

    def choices(node, occupancy):
        if occupancy == 0:
            return {(0, 0): 1}
        if occupancy == 2:
            return {(2, 0): 1}
        return {(1, node): 1, (1, (order - node) % order): 1}

    def add(result, terms):
        for key, count in terms.items():
            result[key] = result.get(key, 0) + count

    @lru_cache(None)
    def children(node, remainder):
        if node % 2:
            return {(0, 0): 1} if remainder == 0 else {}
        left, right = node // 2, (order - node) // 2
        result = {}
        for occupancy in range(min(2, remainder) + 1):
            left_part = combine(choices(left, occupancy), children(left, remainder-occupancy))
            right_part = combine(choices(right, occupancy), children(right, remainder-occupancy))
            add(result, combine(left_part, right_part))
        return result

    root = order // 4
    result = {}
    for occupancy in range(min(2, level) + 1):
        add(result, combine(choices(root, occupancy), children(root, level-occupancy)))
    return [result.get((size, r), 0) for r in range(order)]


def antipodal_test(order, size, level):
    direct = [0] * order
    target = (level,) * (order // 4)
    for chosen in combinations([j for j in range(1, order) if j != order // 2], size):
        negated = {(j + order // 2) % order for j in chosen}
        if signature_of(set(chosen), order) == target and signature_of(negated, order) == target:
            direct[sum(chosen) % order] += 1
    require(uniform_coincidences(order, size, level) == direct, "antipodal overlap census")


def antipodal_bound(order, size, level, levels, deviations, limit, expectations):
    """Use two bins at +1, and independent or explicitly counted bins at -1."""
    n = 2**30
    h = n // order
    constant = (level,) * (order // 4)
    count = oriented_counter(order, size)
    central = count(constant)
    overlap = uniform_coincidences(order, size, level)
    pool = signature_pool(order//4, levels, deviations, size, limit)
    for field, root, bins, expected in expectations:
        other_root = (root + size * (order//2)) % order
        plus = central[root] + central[root + order]
        minus = central[other_root] + central[other_root + order]
        disjoint = []
        for _, signature in pool:
            if sum(signature) != sum(constant):
                histogram = count(signature)
                disjoint.extend((histogram[other_root], histogram[other_root + order]))
        plus_minus = plus + minus - overlap[root]
        total = plus_minus + sum(sorted(disjoint, reverse=True)[:bins-4])
        require(total > field * n, "two-anchor list misses budget")
        gain = (h + 1) // bins
        errors = n - (size + 1)*h + 1 - gain
        require((total, gain, errors) == expected, f"unexpected antipodal receipt {total, gain, errors}")
        print(f"P{field} rate 1/{order//(size-1)} two anchors: bins={bins} root={root} "
              f"words={total} overlap={overlap[root]} gain={gain} first_failure<={errors}")


def external_reserve_bounds():
    """Two full anchor fibers, with the common vanisher on a third fiber."""
    order, size, root, level = 128, 17, 16, 2
    n = 2**30
    h = n // order
    pool = signature_pool(32, range(1, 4), 2, size, 150)
    count = oriented_counter(order, size)
    central = count((level,) * 32)
    opposite = (root + size * (order // 2)) % order
    overlap = uniform_coincidences(order, size, level)[root]
    common = sum(central[r] + central[r + order] for r in (root, opposite)) - overlap

    # The integer leaf sum is fixed by negation. Distinct weights give disjoint
    # sets, even when their word values are supplied by opposite anchor fibers.
    examples = (
        (1, 13, ((48, 0, 4), (68, 1, 11), (60, 0, 7)),
         1245773409, 1077692870, 922101604),
        (2, 28, ((48, 0, 4), (68, 0, 16), (60, 1, 16), (66, 1, 10), (72, 0, 6)),
         2539921351, 2197233550, 922447288),
    )
    for field, capacity, groups, expected_pool, expected_list, expected_error in examples:
        used = [2, 2]
        total = common
        weights = [w for w, _, _ in groups]
        require(len(set(weights)) == len(weights) and 64 not in weights, "overlapping weight classes")
        for weight, anchor, number in groups:
            r = (root, opposite)[anchor]
            populations = []
            for _, signature in pool:
                if sum(signature) == weight:
                    row = count(signature)
                    populations.extend((row[r], row[r + order]))
            require(number <= len(populations), "too few signature labels")
            total += sum(sorted(populations, reverse=True)[:number])
            used[anchor] += number
        require(used == [capacity, capacity] and total == expected_pool, "selected anchor counts")
        # Each 17-set misses precisely 109 of the 126 ordinary quotient points.
        numerator = (order - 2 - size) * total
        surviving = (numerator + order - 3) // (order - 2)
        gain = h // capacity
        errors = n - (size + 1) * h + 1 - gain
        require(surviving == expected_list and surviving > field * n, "over-budget surviving family")
        require(errors == expected_error, "error radius")
        print(f"P{field} third-fiber reserve: bins={used}, pool={total}, "
              f"words>={surviving}, gain={gain}, first_failure<={errors}")


def main():
    external_reserve_bounds()
    for order, size, level in ((8, 2, 1), (16, 4, 1), (16, 6, 2)):
        antipodal_test(order, size, level)
    antipodal_bound(64, 33, 5, range(3, 8), 3, 30,
                    ((1, 8, 6, (1083512160, 2796202, 500520279)),
                     (2, 4, 13, (2198117102, 1290555, 502025926))))
    antipodal_bound(128, 17, 2, range(1, 4), 2, 150,
                    ((1, 16, 22, (1075279395, 381300, 922365581)),
                     (2, 64, 47, (2155690992, 178481, 922568400))))
    small_check(8, 2, 97)
    small_check(16, 4, 97)
    primes = (365375409332725729550921208179070755120141565953,
              730750818665451459101842416358141509841924915201)
    for index, p in enumerate(primes, 1):
        require((p-1) % 2**30 == 0 and p // 2**128 == index*2**30, "field parameters")
    production(64, 33, range(3, 8), 3, 30,
               ((7, 4, 1193490135, 2396745, 500919736),
                (14, 16, 2295961316, 1198372, 502118109)))
    production(64, 17, range(1, 6), 3, 4200,
               ((1741, 1, 1074248723, 9636, 771742301),
                (3862, 1, 2147920993, 4344, 771747593)))
    production(128, 17, range(1, 4), 2, 150,
               ((24, 16, 1114017923, 349525, 922397356),
                (48, 0, 2147800794, 174762, 922572119)))


if __name__ == "__main__":
    main()
