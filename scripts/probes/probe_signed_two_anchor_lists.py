"""Reproduce the two-anchor list bounds and exhaust a length-128 test over F257."""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations
from math import isqrt, prod

from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_reciprocal_fiber_lists import signature_of


class LocatorCounts:
    """Subset counts indexed by cardinality and exponent sum modulo twice the order."""

    def __init__(self, order, size):
        self.order = order
        self.size = size

    def weights(self, node, occupied):
        # Exponents of the chosen members of {node, M-node}.
        return ((0,), (node, self.order - node), (self.order,))[occupied]

    def accumulate(self, out, node, occupied, left, right):
        for (i, a), first in left.items():
            for (j, b), second in right.items():
                size = occupied + i + j
                if size <= self.size:
                    for e in self.weights(node, occupied):
                        out[size, (a + b + e) % (2 * self.order)] += first * second

    @lru_cache(None)
    def single(self, node, vector):
        out = Counter()
        for a in range(min(2, min(vector)) + 1):
            if len(vector) == 1:
                if vector[0] == a:
                    out.update((a, e) for e in self.weights(node, a))
                continue
            h = len(vector) // 2
            rest = tuple(x - a for x in vector)
            left = self.single(node // 2, rest[:h])
            right = self.single((self.order - node) // 2, rest[h:])
            self.accumulate(out, node, a, left, right)
        return out

    @lru_cache(None)
    def paired(self, node, v, w, a, b):
        """Count joint signatures. a,b are occupancies of the node and its sibling."""
        if min(v) < a or min(w) < b:
            return {}
        if len(v) == 1:
            if (v[0], w[0]) != (a, b):
                return {}
            return Counter((a, e) for e in self.weights(node, a))
        out = Counter()
        h = len(v) // 2
        vr = tuple(x - a for x in v)
        wr = tuple(x - b for x in w)
        # Negating a root exchanges siblings at every level and fixes the root node.
        for c in range(3):
            for d in range(3):
                left = self.paired(node // 2, vr[:h], wr[:h], c, d)
                right = self.paired((self.order - node) // 2, vr[h:], wr[h:], d, c)
                self.accumulate(out, node, a, left, right)
        return out

    def joint_count(self, v, w, e):
        return sum(self.paired(self.order // 4, v, w, a, a).get((self.size, e), 0)
                   for a in range(3))

    def union_lower(self, plus, minus):
        def population(modes):
            return sum(self.single(self.order // 4, v)[self.size, e] for v, e in modes)

        # Dropping the rotated exponent condition can only overcount the intersection.
        overlap = sum(self.joint_count(v, w, e) for v, e in plus for w in {s for s, _ in minus})
        return population(plus), population(minus), overlap


def production():
    m, n, h = 64, 2**30, 2**24
    census = LocatorCounts(m, 33)
    flat = (5,) * 16
    left = (6,) * 8 + (5,) * 8
    right = left[::-1]
    last = (5,) * 12 + (6,) * 4
    plus1 = [(flat, 120), (flat, 56), (right, 56)]
    minus1 = [(flat, 88), (flat, 24), (left, 24)]
    plus2 = [(v, e) for v in (flat, right, left) for e in (124, 60)]
    minus2 = [(v, e) for v in (flat, right, left) for e in (92, 28)] + [(last, 28)]
    first = 365375409332725729550921208179070755120141565953
    second = 730750818665451459101842416358141509841924915201
    for p, plus, minus, target in (
            (first, plus1, minus1, (545514807, 545514807, 8242560, 500520279)),
            (second, plus2, minus2, (1035846314, 1193490135, 45511668, 502025926))):
        product = plus[0][1] % m
        require(all(e % m == product for _, e in plus), "single original root product")
        require(all((e - 33 * (m//2)) % m == product for _, e in minus),
                "same original product at the other anchor")
        require(len(set(plus)) == len(plus) and len(set(minus)) == len(minus), "disjoint modes")
        rows = census.union_lower(plus, minus)
        gain = (h + 1) // (len(plus) + len(minus))
        require(max(len(plus), len(minus)) * gain <= h, "both anchor capacities")
        errors = n - (34 * h - 1 + gain)
        require((*rows, errors) == target, "production certificate")
        words = rows[0] + rows[1] - rows[2]
        require((p - 1) % n == 0 and words > p // 2**128, "smooth field and budget")
        print(f"budget={p//2**128}, words>={words}, gain={gain}, first failure<={errors}")
    paley = 536870909
    require(all(paley % divisor for divisor in range(2, isqrt(paley) + 1)), "Paley prime")
    require(paley % 4 == 1 and 2*(paley+1) == n-4, "Paley type-II order")


def small():
    p, n, order, size = 257, 128, 16, 5
    h = n // order
    xs = [pow(9, j, p) for j in range(n)]
    z = pow(9, n // (2 * order), p)
    ys = [pow(z, 2*j, p) for j in range(order)]
    require(len(set(xs)) == n and pow(z, order, p) == p-1, "primitive roots")
    census = LocatorCounts(order, size)
    source = [j for j in range(1, order) if j != order // 2]
    single = Counter()
    joint = Counter()
    groups = defaultdict(list)
    def mode(indices):
        return signature_of(set(indices), order), sum(indices) % (2*order)
    def leaf_order(node):
        if node % 2:
            return [node]
        return leaf_order(node//2) + leaf_order((order-node)//2)
    imaginary = pow(z, order//2, p)
    weights = [imaginary * (pow(z, -j, p) - pow(z, j, p)) % p
               for j in leaf_order(order//4)]
    def signed_value(vector, exponent):
        return pow(-imaginary, size, p) * pow(z, exponent, p) * prod(
            pow(weight, count, p) for weight, count in zip(weights, vector)) % p
    values = defaultdict(set)
    for choice in combinations(source, size):
        v, e = mode(choice)
        w, f = mode(tuple((j + order//2) % order for j in choice))
        single[v, e] += 1
        joint[v, w, e] += 1
        locator = fiber_polynomial([ys[j] for j in choice], p)
        require(signed_value(v, e) == evaluate(locator, 1, p) and
                (-1)**size * signed_value(w, f) % p == evaluate(locator, -1, p),
                "exact signed values at both anchors")
        values[1, v, e].add(evaluate(locator, 1, p))
        values[-1, w, f].add(evaluate(locator, -1, p))
        groups[e % order].append(((v, e), (w, f), locator))
    require(all(len(x) == 1 for x in values.values()), "sign fully determines actual locator")
    vectors = {v for v, _ in single}
    for v in vectors:
        computed = census.single(order//4, v)
        require(all(computed[size, e] == single[v, e] for e in range(2*order)), "single recurrence")
    for v in vectors:
        for w in vectors:
            require(all(census.joint_count(v, w, e) == joint[v, w, e] for e in range(2*order)),
                    "joint recurrence including zero populations")
    members = groups[1]
    plus, minus = (Counter(row[i] for row in members).most_common(1)[0][0] for i in range(2))
    selected = [loc for a, b, loc in members if a == plus or b == minus]
    require(any(a == plus and b != minus for a, b, _ in members) and
            any(a != plus and b == minus for a, b, _ in members), "both anchors add words")
    gain = (h+1)//2
    anchors = [[x for x in xs if pow(x, h, p) == y] for y in (1, p-1)]
    reserve = (anchors[0][gain:] + anchors[1][gain:])[:h-1]
    common = fiber_polynomial(reserve, p)
    fixed = selected[0][0]
    require(all(loc[0] == fixed for loc in selected), "common product")
    center = {}
    for x in xs:
        y = pow(x, h, p)
        value = pow(y, size, p) + fixed
        for sign, anchor, idx in [(1, plus, 0), (-1, minus, 1)]:
            if x in anchors[idx][:gain]:
                value -= next(iter(values[sign, anchor[0], anchor[1]]))
        center[x] = evaluate(common, x, p) * value * pow(y, -1, p) % p
    words = set()
    for loc in selected:
        head = [0] * ((size-2)*h+1)
        head[::h] = [(-c) % p for c in loc[1:-1]]
        poly = poly_mul(common, head, p)
        require(len(poly) <= (size-1)*h, "valid RS dimension")
        word = tuple(evaluate(poly, x, p) for x in xs)
        require(sum(a == center[x] for a, x in zip(word, xs)) >= (size+1)*h-1+gain,
                "actual common-center agreements")
        words.add(word)
    require(len(words) == len(selected), "distinct interleavable words")
    print(f"F257 length 128: {len(words)} distinct words checked at {len(xs)} coordinates.")


if __name__ == "__main__":
    small()
    production()
