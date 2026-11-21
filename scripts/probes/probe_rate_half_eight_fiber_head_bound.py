"""Exact dual bounds for converting the order-eight prescribed-product list to MCA.

The coordinate classes are calculated in the repository's first prime field.
Only integer inequalities are used. See the November 21 entry in docs/research/proximity-gap/PROGRESS.md
for the pointwise interpretation and the predecessor radius.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations
from math import prod

PRIME = 365375409332725729550921208179070755120141565953
GENERATOR = 303645430271030343624574566109998498685964493478
LENGTH = 2**30

# Each triple gives head weights, the multiplier of the label count, and
# the cost of a coordinate where the common polynomial multiplier vanishes.
CERTIFICATES = {
    4: [
        ((0, 0, 2, 2), 1, 1),
        ((0, 0, 3, 3), 1, 2),
        ((1, 1, 1, 1), 1, 1),
        ((3, 3, 3, 6), 2, 7),
    ],
    5: [
        ((0, 0, 0, 3, 3), 1, 2),
        ((0, 3, 3, 3, 3), 2, 4),
        ((1, 1, 1, 6, 6), 4, 3),
        ((2, 2, 2, 2, 2), 3, 1),
    ],
    6: [
        ((0, 0, 3, 3, 3, 3), 2, 4),
        ((0, 3, 3, 3, 6, 6), 4, 5),
        ((1, 1, 1, 2, 2, 3), 2, 2),
    ],
    7: [((3, 3, 6, 6, 9, 9, 12), 10, 8)],
}


def quotient_values():
    root = pow(GENERATOR, LENGTH // 8, PRIME)
    nodes = [pow(root, j, PRIME) for j in range(8)]
    if len(set(nodes)) != 8 or pow(root, 8, PRIME) != 1:
        raise ValueError("quotient generator does not have order eight")
    # The five-element root subsets have the same product since their
    # three-element complements have product one. The common received
    # term and the invertible per-fiber scale do not change equalities.
    return [
        [prod(x - nodes[t] for t in range(8) if t not in errors) % PRIME
         for x in nodes]
        for errors in combinations(range(8), 3) if sum(errors) % 8 == 0
    ]


def equality_classes(values, heads):
    result = []
    for fiber in range(8):
        partition = defaultdict(list)
        for local, head in enumerate(heads):
            partition[values[head][fiber]].append(local)
        result.append(tuple(partition.values()))
    return result


def bound(partitions, weights, label_weight, root_cost):
    total = sum(weights)
    fiber_bounds = []
    for groups in partitions:
        distinct = len(groups)
        # On the line, at most one label and one equality class of agreements.
        # Off the line, at most one label for each distinct head value.
        # At a zero of the multiplier all heads can agree simultaneously.
        on_line = max(sum(weights[i] for i in group) for group in groups)
        on_line += label_weight * int(distinct > 1)
        off_line = label_weight * distinct
        at_root = total - root_cost
        fiber_bounds.append(max(on_line, off_line, at_root))
    return Fraction(sum(fiber_bounds) - 8 * label_weight + root_cost, total)


def main():
    values = quotient_values()
    if len(values) != 7:
        raise ValueError("wrong number of quotient heads")
    for count, certificates in CERTIFICATES.items():
        checked = 0
        for heads in combinations(range(7), count):
            partitions = equality_classes(values, heads)
            if not any(bound(partitions, weights, label_weight, root_cost) <= Fraction(16, 3)
                       for template, label_weight, root_cost in certificates
                       for weights in set(permutations(template))):
                raise AssertionError(f"no dual bound for heads {heads}")
            checked += 1
        print(f"{count} active heads: {checked} subsets, minimum joint core <= 16s/3")


if __name__ == "__main__":
    main()
