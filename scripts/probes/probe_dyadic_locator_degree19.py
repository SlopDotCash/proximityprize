"""Verify the two-moment cap for 19 roots on the named order-256 quotients."""

from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb

from probe_dyadic_locator_degree_caps import PRIMES, first_sum_cap


ROOTS = (
    322599146406626103794850093414153468931889947837,
    570111643962194518645012562298052832947617858734,
)


def root_table(order, root, prime):
    if pow(root, order // 2, prime) != prime - 1 or pow(root, order, prime) != 1:
        raise ArithmeticError("wrong order of the proposed root")
    return [pow(root, i, prime) for i in range(order)]


def canonical_reduced_multisets(order, size):
    """One cyclic translate of each multiset with no antipodal cancellation."""
    for tail in combinations_with_replacement(range(order), size - 1):
        sites = (0,) + tail
        if any(site + order // 2 in sites for site in sites):
            continue
        gaps = tuple(y - x for x, y in zip(sites, sites[1:])) + (order - sites[-1],)
        if gaps[-1] != max(gaps):
            continue
        # Anchor just after a largest gap, breaking ties by the cyclic gap sequence.
        if any(gaps[i-1] == gaps[-1] and gaps[i:] + gaps[:i] < gaps
               for i in range(1, size)):
            continue
        yield sites


def verify_short_sums(order, fields):
    """Check nonzero, disjoint rotation orbits across all four sizes at each prime."""
    tables = [root_table(order, root, p) for p, root in fields]
    seen = [set() for _ in fields]
    counts = []
    for size in range(1, 5):
        count = 0
        for sites in canonical_reduced_multisets(order, size):
            for (p, _), powers, values in zip(fields, tables, seen):
                orbit = pow(sum(powers[i] for i in sites), order, p)
                if not orbit or orbit in values:
                    raise ArithmeticError(f"short-sum collision at {p}, {sites}")
                values.add(orbit)
            count += 1
        total = sum(comb(order // 2, j) * 2**j * comb(size - 1, j - 1)
                    for j in range(1, size + 1))
        if order * count != total:
            raise ArithmeticError(f"incomplete order-{order} orbit census at size {size}")
        counts.append(count)
    return counts


def signed_imbalance_cap(blocks, doubles, singles, distance):
    """Shorten a signed vector on prescribed entries of each absolute value."""
    bounds = []
    for i in range(doubles + 1):
        for j in range(singles + 1):
            gap = distance - 2 * (4 * (doubles - i) + singles - j)
            if gap > 0:
                choices = comb(blocks, i) * comb(blocks - i, j) * 2**(i+j)
                pins = comb(doubles, i) * comb(singles, j)
                bounds.append(choices * (distance // gap) // pins)
    return min(bounds)


def phase_cap(zeros, active, singles):
    """Cap phases on fixed supports and after marking all but four active blocks."""
    weight = singles + 2 * active
    binary = 1 if weight < 9 else 2**weight // sum(comb(weight, i) for i in range(5))
    fixed_support = comb(zeros, active) * binary

    free_blocks = min(4, active)
    free_signs = min(singles, 4 - free_blocks)
    marks = comb(zeros, active - free_blocks) * 4**(active - free_blocks)
    by_marking = marks * 2**(singles - free_signs) // comb(active, free_blocks)
    return min(fixed_support, by_marking)


def degree_cap(order, size, completion_cap):
    """Return the low-weight charge and charges by number of double imbalances."""
    blocks = order // 4
    low_weight = 0
    for weight in range(size % 2, min(5, size) + 1, 2):
        pins = max(0, weight - 4)
        count = comb(order // 2, pins) * 2**pins // comb(weight, pins)
        low_weight += count * completion_cap((size - weight) // 2)

    by_doubles = []
    for doubles in range(min(blocks, size // 2) + 1):
        total = 0
        for singles in range(size % 2, min(blocks - doubles, size - 2*doubles) + 1, 2):
            orientations = signed_imbalance_cap(blocks, doubles, singles, 31)
            pairs = (size - 2*doubles - singles) // 2
            for triples in range(min(singles, pairs) + 1):
                zero_blocks = blocks - doubles - singles
                for full in range(min(zero_blocks, (pairs - triples) // 2) + 1):
                    active = pairs - triples - 2*full
                    if active > zero_blocks - full or singles + 2*active <= 5:
                        continue
                    labels = comb(singles, triples) * comb(zero_blocks, full)
                    total += orientations * labels * phase_cap(zero_blocks - full, active, singles)
        by_doubles.append(total)
    return low_weight, by_doubles


def check_small_domain():
    order, prime = 16, 998244353
    root = pow(3, (prime - 1) // order, prime)
    powers = root_table(order, root, prime)
    verify_short_sums(order, [(prime, root)])
    # Enumerate every unreduced multiset, separately from the orbit method.
    reduced_by_sum = {}
    for size in range(5):
        for sites in combinations_with_replacement(range(order), size):
            oriented = tuple(sites.count(j) - sites.count(j + order // 2)
                             for j in range(order // 2))
            value = sum(powers[j] for j in sites) % prime
            if reduced_by_sum.setdefault(value, oriented) != oriented:
                raise ArithmeticError("direct small-domain collision")

    if 30**(order // 8) >= prime:
        raise ArithmeticError("small control lacks the separation bound")
    # Use actual first-moment fiber sizes for the half-order completion in this control.
    sums = {}
    for size in range(5):
        counts = Counter(sum(powers[2*j] for j in sites) % prime
                         for sites in combinations(range(order // 2), size))
        sums[size] = max(counts.values())
    blocks = order // 4
    for size in (7, 8, 9):
        counts = Counter()
        phases = Counter()
        for sites in combinations(range(order), size):
            sites = set(sites)
            first = sum(powers[j] for j in sites) % prime
            second = sum(powers[2*j % order] for j in sites) % prime
            counts[first, second] += 1
            imbalances = []
            triples, full = [], []
            active = 0
            for j in range(blocks):
                pos = int(j in sites) + int(j + 2*blocks in sites)
                neg = int(j + blocks in sites) + int(j + 3*blocks in sites)
                imbalances.append(pos - neg)
                if pos + neg == 3:
                    triples.append(j)
                if pos + neg == 4:
                    full.append(j)
                if pos == neg == 1:
                    active += 1
            singles = sum(abs(x) == 1 for x in imbalances)
            weight = singles + 2*active
            if weight > 5:
                key = (first, tuple(imbalances), tuple(triples), tuple(full))
                phases[key] += 1
                zeros = imbalances.count(0) - len(full)
                if phases[key] > phase_cap(zeros, active, singles):
                    raise ArithmeticError(("phase count", key, phases[key]))
        low, charges = degree_cap(order, size, sums.__getitem__)
        if max(counts.values()) > low + sum(charges):
            raise ArithmeticError((size, max(counts.values()), low, charges))
    # A field with accidental short sums must be rejected even at small order.
    try:
        verify_short_sums(8, [(17, 2)])
    except ArithmeticError as error:
        if not str(error).startswith("short-sum collision"):
            raise
    else:
        raise ArithmeticError("missed a known short-sum collision")


def main():
    check_small_domain()
    if any(p <= 30**32 for p in PRIMES):
        raise ArithmeticError("the named fields do not meet the separation bound")
    counts = verify_short_sums(256, list(zip(PRIMES, ROOTS)))
    low, charges = degree_cap(256, 19, first_sum_cap)
    total = low + sum(charges)
    if counts != [1, 128, 10923, 699136] or low != 4666368 or total != 476935528:
        raise ArithmeticError((counts, low, charges, total))
    print("short-sum orbits checked at each prime:", counts)
    print("degree 19 low-weight cap:", low)
    print("degree 19 caps by number of double imbalances:", charges)
    print("degree 19 cap:", total)


if __name__ == "__main__":
    main()
