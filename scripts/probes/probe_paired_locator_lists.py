"""Certify production list populations with overlapping opposite serving fibers."""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations

from probe_oriented_fiber_lists import oriented_counter, require, signature_pool
from probe_reciprocal_fiber_lists import signature_of


def subtree_key(signature):
    """Inherited offsets contribute a multiple of the leaf count in every subtree."""
    leaves = len(signature)
    proper = [2**d for d in range(1, leaves.bit_length() - 1)]
    residues = tuple(sum(signature[i:i+width]) % width
                     for width in proper for i in range(0, leaves, width))
    return sum(signature), residues


def paired_children(order, node, positive, negative, a, b):
    """The two subtrees have the same leaves after swapping sibling occupancies."""
    half = len(positive) // 2
    left_pos = tuple(v-a for v in positive[:half])
    left_neg = tuple(v-b for v in negative[:half])
    right_pos = tuple(v-a for v in positive[half:])
    right_neg = tuple(v-b for v in negative[half:])
    difference, remainder = divmod(sum(left_pos)-sum(left_neg), half)
    if remainder:
        return
    for left in range(3):
        right = left - difference
        if 0 <= right <= 2:
            yield ((node//2, left_pos, left_neg, left, right),
                   ((order-node)//2, right_pos, right_neg, right, left))


class JointCensus:
    """Count original and antipodally rotated signatures at once, by cardinality and product."""

    def __init__(self, order, size):
        self.order = order
        self.size = size
        # A digit counts subsets of fewer than order roots, hence is below 2**order.
        self.width = order * order
        self.mask = (1 << self.width) - 1
        self.digit = (1 << order) - 1

    def fold(self, value):
        """Reduce a convolution modulo Z**order-1, using base-2**order digits."""
        return (value & self.mask) + (value >> self.width)

    @lru_cache(None)
    def subtree(self, node, positive, negative, a, b):
        """a,b count the occupied roots at this node before and after negation."""
        leaves = len(positive)
        if a > min(positive) or b > min(negative):
            return ()
        if sum(positive) - sum(negative) != leaves * (a - b):
            return ()
        order = self.order
        if leaves == 1:
            if positive[0] != a or negative[0] != b:
                return ()
            weights = 1
            if a == 1:
                weights = (1 << (node*order)) + (1 << ((order-node)*order))
            return ((a, weights),)

        convolution = defaultdict(int)
        for left_args, right_args in paired_children(order, node, positive, negative, a, b):
            left = self.subtree(*left_args)
            right = self.subtree(*right_args)
            for i, first in left:
                for j, second in right:
                    degree = a + i + j
                    if degree <= self.size:
                        convolution[degree] += first * second
        result = []
        for degree, product in convolution.items():
            weights = self.fold(product)
            if a == 1:
                weights = self.fold(weights << (node*order)) + self.fold(weights << ((order-node)*order))
            result.append((degree, weights))
        return tuple(result)

    def population(self, positive, negative, residue):
        """The root inverse pair is fixed by negation, so its two occupancies agree."""
        if subtree_key(positive) != subtree_key(negative):
            return 0
        encoded = sum(dict(self.subtree(self.order//4, positive, negative, a, a)).get(self.size, 0)
                      for a in range(3))
        return (encoded >> (residue*self.order)) & self.digit


def small_control(order, size):
    counts = Counter()
    letters = [j for j in range(1, order) if j != order//2]
    for subset in combinations(letters, size):
        positive = signature_of(set(subset), order)
        negative = signature_of({(j+order//2) % order for j in subset}, order)
        require(subtree_key(positive) == subtree_key(negative), "subtree congruence")
        counts[positive, negative, sum(subset) % order] += 1
    census = JointCensus(order, size)
    signatures = {positive for positive, _, _ in counts}
    for v in signatures:
        for w in signatures:
            for r in range(order):
                require(census.population(v, w, r) == counts[v, w, r], "joint census mismatch")
    print(f"Order {order}: all joint multiplicities match direct enumeration.")


def paired_palettes(order, size, reserved, root, histograms, group_of, groups):
    """Each sign and signature belongs to the unique anchor group assigned its invariant sum."""
    step = order // reserved
    palettes = [[] for _ in range(reserved)]
    for v, histogram in histograms.items():
        group = group_of(sum(v))
        if group is None:
            continue
        for a in groups[group]:
            residue = (root - size*a*step) % order
            palettes[a].extend((histogram[e], v, e) for e in (residue, residue+order))
    return [sorted(row, reverse=True) for row in palettes]


def unsigned_overlap(positive, negative, residue, joint):
    """Discard sign and reserve restrictions for an upper bound on repeated candidates."""
    by_key = []
    for chosen in (positive, negative):
        values = defaultdict(set)
        for _, v, _ in chosen:
            values[subtree_key(v)].add(v)
        by_key.append(values)
    first, second = by_key
    return sum(joint.population(v, w, residue)
               for key, plus in first.items() for v in plus for w in second[key])


def receipt(order, size, reserved, root, histograms, group_of, slots, joint):
    """Assign each rotation-invariant leaf sum to one pair of opposite serving fibers."""
    step = order // reserved
    groups = [[a, a + reserved//2] for a in range(reserved//2 - 1)]
    groups.append([reserved//2 - 1])
    palettes = paired_palettes(order, size, reserved, root, histograms, group_of, groups)
    single, overlaps = [], []
    for anchors in groups:
        chosen = [palettes[a][:slots] for a in anchors]
        single.extend(sum(count for count, _, _ in row) for row in chosen)
        if len(anchors) == 2:
            residue = (root - size*anchors[0]*step) % order
            overlaps.append(unsigned_overlap(*chosen, residue, joint))
    h = 2**30 // order
    words = sum(single) - sum(overlaps)
    errors = 2**30 - ((size+1)*h - 1 + h//slots)
    return single, overlaps, words, errors


def production(order, reserved, root, levels, deviations, limit, rows):
    size = 17
    omitted = frozenset(range(0, order, order//reserved))
    count = oriented_counter(order, size, omitted)
    pool = signature_pool(order//4, levels, deviations, size, limit)
    histograms = {tuple(v): count(v) for _, v in pool}
    joint = JointCensus(order, size)
    for budget, slots, group_of, expected in rows:
        observed = receipt(order, size, reserved, root, histograms, group_of, slots, joint)
        require(observed == expected, "production receipt")
        _, _, words, errors = observed
        require(words > budget, "list below budget")
        print(f"rate=1/{order//16} budget={budget} slots={slots} "
              f"words>={words} errors={errors}")


def assigned_groups(groups):
    lookup = {}
    for index, scores in enumerate(groups):
        for score in scores:
            require(score not in lookup, "score assigned twice")
            lookup[score] = index
    return lookup.get


def main():
    small_control(8, 3)
    small_control(16, 4)
    production(64, 4, 1, range(1, 6), 3, 12000, [
        (2**30, 819, lambda t: (t//3 % 3) % 2,
         ([372608530, 372608530, 338616069], [8986568], 1074846561, 771731452)),
        (2**31, 1912, lambda t: (t % 3) % 2,
         ([758981310, 758981310, 656821212], [26852064], 2147931768, 771743163)),
    ])
    production(128, 8, 16, range(1, 4), 2, 500, [
        (2**30, 6, assigned_groups([[44], [32, 48], [36], [40]]),
         ([134668680, 134668680, 152255492, 152344568, 168091416, 168091416, 186879120],
          [0, 381996, 0], 1096617376, 921348780)),
        (2**31, 12, assigned_groups([[44], [32, 40, 46], [36], [48]]),
         ([269302144, 269302144, 348986116, 349055984, 336155872, 336155872, 257501692],
          [340080, 533312, 423808], 2165162624, 922047831)),
    ])


if __name__ == "__main__":
    main()
