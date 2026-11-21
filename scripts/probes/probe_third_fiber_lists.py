"""Verify quarter- and eighth-rate lists with two split fibers and a third common zero fiber."""

from collections import Counter, defaultdict
from itertools import combinations
from math import prod

from probe_oriented_fiber_lists import oriented_counter, require, signature_pool
from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul
from probe_reciprocal_fiber_lists import signature_of


def plus_class(leaf_sum, modulus, mask):
    """The sum of the leaf signature is invariant under negating every quotient root."""
    return (mask >> ((leaf_sum // 2) % modulus)) & 1


def small_check():
    order, size, prime = 16, 5, 257
    root = next(z for z in range(1, prime) if pow(z, 8, prime) == prime-1)
    for omitted in (1, 4, 5, 9, 12):
        ordinary = set(range(order)) - {0, order//2, omitted}
        census = defaultdict(lambda: [0] * (2*order))
        values = {}
        count = oriented_counter(order, size, omitted)
        for subset in combinations(sorted(ordinary), size):
            signature = signature_of(set(subset), order)
            exponent = sum(subset) % (2*order)
            census[signature][exponent] += 1
            opposite = {(j + order//2) % order for j in subset}
            require(sum(signature) == sum(signature_of(opposite, order)), "signature sum changed")
            value = prod(1 - pow(root, j, prime) for j in subset) % prime
            key = signature, exponent
            require(values.setdefault(key, value) == value, "locator label collision")
        for signature, histogram in census.items():
            require(count(signature) == histogram, "restricted orientation count")
    print("All five restricted order-16 censuses agree with exhaustive enumeration.")


def small_words():
    prime, order, h, size, omitted = 257, 16, 8, 5, 4
    xs = [pow(9, j, prime) for j in range(order*h)]
    labels = [pow(9, h*j, prime) for j in range(order)]
    ordinary = set(range(order)) - {0, order//2, omitted}
    classes = defaultdict(list)
    for subset in combinations(sorted(ordinary), size):
        if sum(subset) % order != 1:
            continue
        signature = signature_of(set(subset), order)
        anchor = 1 if plus_class(sum(signature), 4, 1) else prime-1
        loc = fiber_polynomial([labels[j] for j in subset], prime)
        classes[anchor, evaluate(loc, anchor, prime)].append(loc)
    gain = h//2
    assigned, selected = {}, []
    for anchor in (1, prime-1):
        fibers = [x for x in xs if pow(x, h, prime) == anchor]
        counts = Counter({v: len(locs) for (a, v), locs in classes.items() if a == anchor})
        require(len(counts) >= 2, "two anchor values available")
        for i, (v, _) in enumerate(counts.most_common(2)):
            assigned.update((x, v) for x in fibers[i*gain:(i+1)*gain])
            selected.extend(classes[anchor, v])
    spare = [x for x in xs if pow(x, h, prime) == labels[omitted]][:h-1]
    common = fiber_polynomial(spare, prime)
    c = selected[0][0]
    center = []
    for x in xs:
        y = pow(x, h, prime)
        center.append(evaluate(common, x, prime) * (pow(y, size, prime)+c-assigned.get(x, 0))
                      * pow(y, -1, prime) % prime)
    words = set()
    for loc in selected:
        require(loc[0] == c, "locator constant")
        head = [0]*((size-2)*h+1)
        head[::h] = [(-v) % prime for v in loc[1:-1]]
        message = poly_mul(common, head, prime)
        require(len(message) <= (size-1)*h, "degree bound")
        word = tuple(evaluate(message, x, prime) for x in xs)
        require(sum(v == w for v,w in zip(word, center)) >= size*h+(h-1)+gain, "common center")
        words.add(word)
    require(len(words) == len(selected), "word multiplicity")
    print(f"Verified all {len(words)} codewords on all {len(xs)} coordinates in F257.")


def production(order, levels, deviations, limit, root, omitted, receipts):
    size, n = 17, 2**30
    plus = oriented_counter(order, size, omitted)
    minus_omission = (omitted + order//2) % order
    minus = oriented_counter(order, size, minus_omission)
    minus_root = (root + size*order//2) % order
    groups = defaultdict(lambda: ([], []))
    for _, signature in signature_pool(order//4, levels, deviations, size, limit):
        ph, mh = plus(signature), minus(signature)
        positive, negative = groups[sum(signature)]
        positive.extend((ph[root], ph[root+order]))
        negative.extend((mh[minus_root], mh[minus_root+order]))

    for field, modulus, mask, bins, expected_words, expected_errors in receipts:
        ps, ns = [], []
        for leaf_sum, (positive, negative) in groups.items():
            if plus_class(leaf_sum, modulus, mask):
                ps.extend(positive)
            else:
                ns.extend(negative)
        words = sum(sorted(ps, reverse=True)[:bins]) + sum(sorted(ns, reverse=True)[:bins])
        h = n // order
        gain = h // bins
        errors = n - ((size + 1)*h - 1 + gain)
        require(words == expected_words and words > field*n, "population certificate")
        require(errors == expected_errors, "agreement certificate")
        print(f"prime={field} rate=1/{order//(size-1)} bins_per_anchor={bins} "
              f"population={words} gain={gain} errors={errors}")


def main():
    small_check()
    small_words()
    production(64, range(1, 6), 3, 12000, 1, 16,
               [(1, 8, 229, 1123, 1074257931, 771736998),
                (2, 7, 90, 2547, 2147852051, 771745350)])
    production(128, range(1, 4), 2, 150, 16, 32,
               [(1, 4, 1, 14, 1147731928, 922147695),
                (2, 7, 57, 29, 2194094160, 922457619)])


if __name__ == "__main__":
    main()
