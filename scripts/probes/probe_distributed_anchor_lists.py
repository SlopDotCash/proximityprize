"""Check production list witnesses with common roots spread across all reserved fibers."""

from collections import Counter
from functools import lru_cache
from itertools import combinations

from probe_oriented_fiber_lists import oriented_counter, require, signature_pool
from probe_paired_locator_lists import (
    JointCensus, assigned_groups, paired_children, paired_palettes, subtree_key, unsigned_overlap,
)
from probe_reciprocal_fiber_lists import signature_of


class SignedJointCensus:
    """Count both signed modes, retaining the parity of the upper-half occupancy."""

    def __init__(self, order, size, omitted):
        self.order = order
        self.size = size
        self.omitted = frozenset(omitted)
        require(all((-j) % order in self.omitted and (j+order//2) % order in self.omitted
                    for j in self.omitted), "reserved set must be stable under both involutions")
        # Histograms have 2M digits of M bits. Even intermediate sums count fewer than 2^M sets.
        self.width = 2 * order * order
        self.mask = (1 << self.width) - 1
        self.digit = (1 << order) - 1

    def fold(self, value):
        reduced = (value & self.mask) + (value >> self.width)
        return (reduced & self.mask) + (reduced >> self.width)

    def shift(self, row, exponent):
        return self.fold(row << (self.order * exponent))

    @lru_cache(None)
    def subtree(self, node, positive, negative, a, b):
        leaves = len(positive)
        if min(positive) < a or min(negative) < b:
            return ()
        if sum(positive) - sum(negative) != leaves * (a-b) or (a and node in self.omitted):
            return ()
        if leaves == 1:
            if (positive[0], negative[0]) != (a, b):
                return ()
            joined = {0: (1, 0)}
        else:
            joined = {}
            for left_args, right_args in paired_children(self.order, node, positive, negative, a, b):
                left = self.subtree(*left_args)
                right = self.subtree(*right_args)
                for i, left_even, left_odd in left:
                    for j, right_even, right_odd in right:
                        if i + j + a > self.size:
                            continue
                        even, odd = joined.get(i+j, (0, 0))
                        joined[i+j] = (
                            even + self.fold(left_even*right_even + left_odd*right_odd),
                            odd + self.fold(left_even*right_odd + left_odd*right_even),
                        )

        result = []
        for size, (even, odd) in joined.items():
            if a == 1:
                # The exponent order-node is the upper-half orientation at every tree node.
                even, odd = (
                    self.shift(even, node) + self.shift(odd, self.order-node),
                    self.shift(odd, node) + self.shift(even, self.order-node),
                )
            elif a == 2:
                even, odd = self.shift(odd, self.order), self.shift(even, self.order)
            result.append((size+a, even, odd))
        return tuple(result)

    def population(self, positive, e, negative, f):
        if subtree_key(positive) != subtree_key(negative):
            return 0
        wrap = (e + self.size*(self.order//2) - f) % (2*self.order)
        if wrap not in (0, self.order):
            return 0
        parity = wrap // self.order
        result = 0
        for a in range(3):
            for size, even, odd in self.subtree(self.order//4, positive, negative, a, a):
                if size == self.size:
                    result += ((even, odd)[parity] >> (e*self.order)) & self.digit
        return result


def small_control(order, size, step):
    omitted = range(0, order, step)
    census = SignedJointCensus(order, size, omitted)
    observed = Counter()
    for subset in combinations([j for j in range(order) if j not in omitted], size):
        opposite = {(j + order//2) % order for j in subset}
        v, w = signature_of(set(subset), order), signature_of(opposite, order)
        observed[(v, sum(subset) % (2*order)), (w, sum(opposite) % (2*order))] += 1
    modes = {first for first, _ in observed}
    for first in modes:
        for second in modes:
            require(census.population(*first, *second) == observed[first, second],
                    "signed pair differs from enumeration")
    # Every other pair has at least one empty marginal.
    print(f"Order {order}: checked all {len(modes)**2} pairs of nonempty signed modes.")


def histograms(order, reserved, levels, deviations, limit):
    size = 17
    count = oriented_counter(order, size, range(0, order, order//reserved))
    return {tuple(v): count(v) for _, v in signature_pool(order//4, levels, deviations, size, limit)}


def certificate(order, reserved, root, hist, group_of, ranks, exact, budget, expected):
    groups = [(i, i+reserved//2) for i in range(reserved//2)]
    choices = paired_palettes(order, 17, reserved, root, hist, group_of, groups)
    selected = [[row[i] for i in indices] for row, indices in zip(choices, ranks, strict=True)]
    require(all(len(set(row)) == len(row) for row in selected), "duplicate signed mode at one anchor")
    if exact:
        joint = SignedJointCensus(order, 17, range(0, order, order//reserved))
        overlaps = [sum(joint.population(v, e, w, f) for _, v, e in selected[i]
                        for _, w, f in selected[j]) for i, j in groups]
    else:
        joint = JointCensus(order, 17)
        overlaps = [unsigned_overlap(selected[i], selected[j],
                                     (root-17*i*(order//reserved)) % order, joint) for i, j in groups]

    singles = [sum(count for count, _, _ in row) for row in selected]
    n = 2**30
    h = n // order
    slots = sum(map(len, selected))
    gain = min(h // max(map(len, selected)), ((reserved-1)*h + 1) // slots)
    require(all(len(row)*gain <= h for row in selected), "one anchor over capacity")
    require(slots*gain + h-1 <= reserved*h, "insufficient sites for common roots")
    words = sum(singles) - sum(overlaps)
    errors = n - (18*h-1+gain)
    require(words > budget and (singles, overlaps, words, errors) == expected, "production receipt")
    print(f"rate=1/{order//16} budget={budget} modes={slots} gain={gain} "
          f"words>={words} first_failure<={errors}")


def main():
    small_control(8, 3, 4)
    small_control(16, 5, 4)
    quarter = histograms(64, 4, range(1, 6), 3, 12000)
    certificate(64, 4, 1, quarter, lambda s: 0 if (s//4)%5 < 4 else 1, [range(599)]*4,
                False, 2**30, ([276234019, 267652861]*2, [6930791, 6659874],
                                1074183095, 771730931))
    certificate(64, 4, 1, quarter, lambda s: 0 if (s+2)%5 < 3 else 1, [range(1351)]*4,
                False, 2**31, ([560613009, 531156953]*2, [16350133, 18699241],
                                2148490550, 771742624))
    eighth = histograms(128, 8, range(1, 4), 2, 500)
    certificate(128, 8, 16, eighth, assigned_groups([[36], [32, 48], [44], [40]]), [range(5)]*8,
                False, 2**30, ([140076180, 130789633, 112223900, 155732600,
                                140076180, 130847174, 112223900, 155732600],
                               [0, 287694, 0, 266240], 1077148233, 921278875))
    ranks = [range(11), range(11), (0, 1, 2, 3, 4, 5, 8, 11), range(10),
             range(11), (0, 1, 2, 3, 4, 8, 9, 12, 13, 14, 15),
             (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11), range(10)]
    certificate(128, 8, 16, eighth, assigned_groups([[36], [44], [48], [32, 40]]), ranks,
                True, 2**31, ([308147376, 246901138, 171801200, 315525804,
                               308147376, 246858106, 236108990, 315525804],
                              [317856, 254592, 328626, 532480], 2147582240, 922039409))


if __name__ == "__main__":
    main()
