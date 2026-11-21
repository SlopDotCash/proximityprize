"""Verify the split across several quotient fibers at the named rate 1/16.

Run with python3 -O scripts/probes/probe_multifiber_sixteenth_lists.py.
The production census uses integer polynomial arithmetic on four small trees.
"""

from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations
from math import comb

from probe_quarter_coset_lists import evaluate, fiber_polynomial, poly_mul, require
from probe_reciprocal_fiber_lists import counts, signature_of


@lru_cache(None)
def shapes(height, degree):
    """Canonical leaf vectors attainable with exactly degree selected roots."""
    if height == 0:
        return {(degree,)} if degree <= 2 else set()
    result = set()
    for a in range(min(2, degree) + 1):
        for i in range(degree - a + 1):
            for left in shapes(height - 1, i):
                for right in shapes(height - 1, degree - a - i):
                    pair = min(left, right) + max(left, right)
                    result.add(tuple(x + a for x in pair))
    return result


@lru_cache(None)
def orbit_size(v):
    """Number of labelled vectors represented under binary subtree swaps."""
    if len(v) == 1:
        return 1
    mid = len(v) // 2
    left, right = v[:mid], v[mid:]
    return orbit_size(left) * orbit_size(right) * (1 if left == right else 2)


def histogram(m_order, spare_order, degree):
    """For each total-leaf-sum residue, count signatures by their exact list size."""
    # Removing the spare subgroup leaves spare_order/2 complete subtrees.
    leaves = m_order // (2 * spare_order)
    blocks = spare_order // 2
    require(leaves > 0 and leaves & (leaves - 1) == 0 and blocks & (blocks - 1) == 0,
            "dyadic forest")
    modulus = 2 * (spare_order - 1)
    representatives = set().union(*(shapes(leaves.bit_length() - 1, d)
                                       for d in range(degree + 1)))
    profiles = Counter()
    for v in representatives:
        poly = counts(v)[:degree + 1]
        low = next(i for i, a in enumerate(poly) if a)
        high = max(i for i, a in enumerate(poly) if a)
        profiles[sum(v) % modulus, low, poly[low:high+1]] += orbit_size(v)

    # Each label belongs to exactly one ordered pair of child signatures.
    for _ in range(blocks.bit_length() - 1):
        by_low = defaultdict(list)
        for (weight, low, cs), number in profiles.items():
            by_low[low].append((weight, cs, number))
        joined = Counter()
        for i in range(degree + 1):
            for j in range(i, degree - i + 1):
                for index, (w, a, num_a) in enumerate(by_low[i]):
                    others = by_low[j][index:] if i == j else by_low[j]
                    for v, b, num_b in others:
                        length = min(degree - i - j + 1, len(a) + len(b) - 1)
                        c = tuple(sum(a[k] * b[t-k]
                                      for k in range(max(0, t-len(b)+1), min(len(a), t+1)))
                                  for t in range(length))
                        while c[-1] == 0:
                            c = c[:-1]
                        swap = 1 if i == j and w == v and a == b else 2
                        joined[(w + v) % modulus, i + j, c] += swap * num_a * num_b
        profiles = joined
    result = defaultdict(Counter)
    for (weight, low, c), number in profiles.items():
        if 0 <= degree - low < len(c) and c[degree-low]:
            result[weight][c[degree-low]] += number
    total = sum(size * number for row in result.values() for size, number in row.items())
    require(total == comb(m_order - spare_order, degree), "all allowed subsets counted once")
    return result


def capture(row, limit):
    """Count the subsets in the largest limit signatures in a residue class."""
    total = 0
    for size, number in sorted(row.items(), reverse=True):
        used = min(number, limit)
        total += used * size
        limit -= used
        if limit == 0:
            break
    return total


def check_histogram_by_enumeration(m_order, spare_order, degree):
    ordinary = [i for i in range(m_order) if i % (m_order // spare_order)]
    signatures = Counter(signature_of(set(t), m_order) for t in combinations(ordinary, degree))
    direct = defaultdict(Counter)
    for sig, size in signatures.items():
        direct[sum(sig) % (2*(spare_order - 1))][size] += 1
    require(histogram(m_order, spare_order, degree) == direct, "independent forest histogram")
    print(f"M={m_order} spare={spare_order}: checked all {sum(signatures.values())} subsets")


def small_check():
    p, n, m_order, spare_order, b = 257, 128, 16, 4, 2
    h = n // m_order
    g = pow(3, (p-1)//n, p)
    xs = [pow(g, i, p) for i in range(n)]
    ys = [pow(g, h*i, p) for i in range(m_order)]
    require(len(set(xs)) == n and len(set(ys)) == m_order, "small group orders")
    step = m_order // spare_order
    ordinary = [i for i in range(m_order) if i % step]
    modulus = 2*(spare_order - 1)
    reference = Counter()
    pools = defaultdict(lambda: defaultdict(list))
    for chosen in combinations(ordinary, b+1):
        sig = signature_of(set(chosen), m_order)
        reference[sig] += 1
        weight = sum(sig) % modulus
        parity = weight % 2
        anchor = (weight // 2 + 1) * step
        relative = {(i-anchor) % m_order for i in chosen}
        shifted = signature_of(relative, m_order)
        require(sum(shifted) % modulus == weight, "rotation-invariant assignment")
        pools[parity, anchor][shifted].append(chosen)
    expected = defaultdict(Counter)
    for sig, freq in reference.items():
        expected[sum(sig) % modulus][freq] += 1
    require(histogram(m_order, spare_order, b+1) == expected, "all small labeled signatures")
    gain = 1
    cap = h // (2*gain)
    groups = defaultdict(dict)
    for (parity, anchor), mapping in pools.items():
        if parity == 0:
            continue
        ordered = sorted(mapping, key=lambda sig: (-len(mapping[sig]), sig))
        for sig in ordered[:cap]:
            for chosen in mapping[sig]:
                group = groups[sum(chosen) % m_order]
                require(chosen not in group, "disjoint anchor pools")
                group[chosen] = anchor
    chosen_pool = max(groups.values(), key=len)
    values = defaultdict(set)
    codewords = {}
    common = fiber_polynomial([x for x in xs if pow(x, h, p) == 1][1:], p)
    for chosen, anchor in chosen_pool.items():
        locator = fiber_polynomial([ys[i] for i in chosen], p)
        head = [(-a) % p for a in locator[1:-1]]
        values[anchor].add(evaluate(head, ys[anchor], p))
        lift = [0]*((len(head)-1)*h+1)
        lift[::h] = head
        codewords[chosen] = poly_mul(common, lift, p)
    fixed = fiber_polynomial([ys[i] for i in next(iter(chosen_pool))], p)[0]
    assignments = {}
    for anchor, modes in values.items():
        require(len(modes)*gain <= h, "room at each anchor")
        sites = [x for x in xs if pow(x,h,p) == ys[anchor]]
        for x, value in zip(sites, sorted(modes)):
            assignments[x] = value
    center = []
    for x in xs:
        y = pow(x,h,p)
        base = (pow(y,b+1,p)+fixed) * pow(y,-1,p) % p
        center.append(evaluate(common,x,p)*assignments.get(x,base) % p)
    actual = set()
    for coeffs in codewords.values():
        word = tuple(evaluate(coeffs,x,p) for x in xs)
        require(len(coeffs) <= b*h and sum(a == c for a,c in zip(word,center))
                >= (b+2)*h-1+gain, "expanded word degree and agreements")
        actual.add(word)
    require(len(values) >= 2 and len(actual) == len(chosen_pool), "distinct multi-anchor words")
    print(f"F_{p} n={n}: {len(actual)} explicit words across {len(values)} anchors")


def main():
    small_check()
    check_histogram_by_enumeration(32, 8, 4)
    check_histogram_by_enumeration(32, 4, 5)
    rows = histogram(128, 8, 9)
    n = 2**30
    h = n//128
    for budget, gain, parity, expected in [(n, 4, 1, 73013231360),
                                          (2*n, 1, 0, 198924785832)]:
        cap = h//(2*gain)
        raw = sum(capture(rows[parity + 2*i], cap) for i in range(7))
        require(raw == expected and raw > 64*budget, "over-budget common product")
        print(f"B={budget} raw={raw} list>={(raw+63)//64} gain={gain} "
              f"first_bad<={n-10*h+1-gain}")


if __name__ == "__main__":
    main()
