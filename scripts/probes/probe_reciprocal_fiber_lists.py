"""Verify reciprocal-pair list witnesses on dyadic multiplicative domains.

Run with python3 -O scripts/probes/probe_reciprocal_fiber_lists.py.
The large checks count quotient subsets using integer arithmetic. Small
checks enumerate all relevant subsets and evaluate actual RS codewords.
"""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, product
from math import comb, prod

from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require


@lru_cache(None)
def counts(signature):
    """Numbers of subsets of each size with this fixed vector of leaf sums."""
    if min(signature) < 0:
        return ()
    if len(signature) == 1:
        a = signature[0]
        return (0,) * a + (comb(2, a),) if a <= 2 else ()
    half = len(signature) // 2
    out = [0] * (4 * len(signature) - 1)
    for a in range(3):
        reduced = tuple(x - a for x in signature)
        left, right = counts(reduced[:half]), counts(reduced[half:])
        ways = comb(2, a)
        for i, x in enumerate(left):
            if x:
                for j, y in enumerate(right):
                    out[a + i + j] += ways * x * y
    return tuple(out)


def candidate_signatures(leaves, levels, deviations):
    """Enumerate the indicated small perturbations of uniform leaf sums."""
    for level in levels:
        for d in range(deviations + 1):
            for indices in combinations(range(leaves), d):
                for changes in product((-1, 1), repeat=d):
                    sig = [level] * leaves
                    for i, change in zip(indices, changes):
                        sig[i] += change
                    yield tuple(sig)


def production_bound(m_order, dimension, budget, levels, deviations):
    """Select disjoint signatures, all with the same root-product parity."""
    n = 2**30
    h = n // m_order
    subset_size = dimension + 1
    by_parity = [[], []]
    for sig in set(candidate_signatures(m_order // 4, levels, deviations)):
        polynomial = counts(sig)
        if len(polynomial) > subset_size and polynomial[subset_size]:
            by_parity[sum(sig) % 2].append(polynomial[subset_size])
    options = []
    for parity, sizes in enumerate(by_parity):
        total = 0
        for k, size in enumerate(sorted(sizes, reverse=True), start=1):
            total += size
            if total > (m_order // 2) * budget:
                gains = h // (2 * k)
                agreements = (dimension + 2) * h - 1 + gains
                options.append((gains, -k, parity, total, n - agreements))
                break
    require(options, "no over-budget product class")
    gain, negative_k, parity, total, errors = max(options)
    require(gain > 0 and 2 * -negative_k * gain <= h, "spare fiber allocation")
    return -negative_k, parity, total, gain, errors


def signature_of(selected, m_order):
    """Read root pair occupancies down the tree headed by exponent M/4."""
    def walk(i, above):
        a = above + (i in selected) + (m_order - i in selected)
        if i % 2:
            return (a,)
        return walk(i // 2, a) + walk((m_order - i) // 2, a)

    return walk(m_order // 4, 0)


def small_check(p, n, m_order, b):
    """Enumerate every quotient subset, then construct a split-fiber center."""
    g = next(pow(a, (p - 1) // n, p) for a in range(2, p)
             if pow(a, (p - 1) // 2, p) == p - 1)
    h = n // m_order
    xs = [pow(g, i, p) for i in range(n)]
    ys = [pow(g, i * h, p) for i in range(m_order)]
    require(len(set(xs)) == n and len(set(ys)) == m_order, "smooth orders")
    ordinary = [i for i in range(1, m_order) if i != m_order // 2]
    totals = Counter()
    values = defaultdict(set)
    members = defaultdict(list)
    for chosen in combinations(ordinary, b + 1):
        signature = signature_of(set(chosen), m_order)
        exponent = sum(chosen) % m_order
        root_value = prod((1 - ys[i]) for i in chosen) % p
        totals[signature] += 1
        values[signature, exponent].add(root_value)
        members[signature, exponent].append(chosen)
        require(sum(signature) % 2 == exponent % 2, "product parity")
    require(sum(totals.values()) == comb(m_order - 2, b + 1), "all subsets")
    require(all(counts(s)[b + 1] == v for s, v in totals.items()), "tree counts")
    require(all(len(group) <= 2 for group in values.values()), "two values per signature")
    # Combine two signatures on the same product class to exercise the allocation.
    signature, exponent = max(members, key=lambda key: len(members[key]))
    other = max((s for s, e in members if e == exponent and s != signature),
                key=lambda s: len(members[s, exponent]))
    chosen_sets = members[signature, exponent] + members[other, exponent]
    locators = [fiber_polynomial([ys[i] for i in chosen], p) for chosen in chosen_sets]
    fixed = locators[0][0]
    require(all(poly[0] == fixed for poly in locators), "single locator constant")
    anchor = [x for x in xs if pow(x, h, p) == 1]
    reserved = [x for x in xs if pow(x, h, p) == p - 1]
    common = fiber_polynomial(reserved[1:], p)
    heads = [[(-a) % p for a in loc[1:-1]] for loc in locators]
    modes = sorted({evaluate(f, 1, p) for f in heads})
    require(1 < len(modes) <= 4 and h >= len(modes), "nontrivial split")
    gain = h // len(modes)
    assigned = {x: modes[i % len(modes)] for i, x in enumerate(anchor)}
    center = {}
    for x in xs:
        y = pow(x, h, p)
        base = (pow(y, b + 1, p) + fixed) * pow(y, -1, p)
        center[x] = evaluate(common, x, p) * assigned.get(x, base) % p
    words = set()
    for head in heads:
        composition = [0] * ((len(head) - 1) * h + 1)
        composition[::h] = head
        coefficients = poly_mul(common, composition, p)
        require(len(coefficients) <= b * h, "degree below dimension")
        word = tuple(evaluate(coefficients, x, p) for x in xs)
        agreements = sum(w == center[x] for w, x in zip(word, xs))
        require(agreements >= (b + 2) * h - 1 + gain, "actual agreements")
        words.add(word)
    require(len(words) == len(chosen_sets), "distinct codewords")
    print(f"F_{p} n={n} M={m_order}: {len(words)} explicit words, gain {gain}")


def main():
    for board in [(257, 128, 16, 4), (641, 128, 16, 5), (97, 32, 8, 2)]:
        small_check(*board)
    primes = (365375409332725729550921208179070755120141565953,
              730750818665451459101842416358141509841924915201)
    expected = ((501219329, 771744959, 922484737), (502118109, 771749148, 922611581))
    for index, p in enumerate(primes, start=1):
        n = 2**30
        budget = p // 2**128
        require((p - 1) % n == 0 and budget == index * n, "named field parameters")
        cases = [(64, 32, (4, 5, 6), 2), (64, 16, (3,), 3), (128, 16, (1, 2, 3), 1)]
        for (m_order, b, levels, changes), expected_errors in zip(cases, expected[index - 1]):
            k, parity, total, gain, errors = production_bound(
                m_order, b, budget, levels, changes)
            require(errors == expected_errors, "published error count")
            print(f"P{index} 1/{m_order//b}: signatures={k} parity={parity} "
                  f"subsets={total} gain={gain} first_bad<={errors}")


if __name__ == "__main__":
    main()
