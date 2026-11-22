"""Verify the two-moment cap for 19 roots on the named order-256 quotients."""

from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import comb

from probe_dyadic_locator_degree_caps import (
    PRIMES, first_sum_cap, first_sum_product_cap, full_lift_cap, mixed_cap, unlifted_orders,
)


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


def phase_cap(zeros, active, singles, unique_terms=4):
    """Use Hamming balls and shorten on unmarked phases with unique short sums."""
    weight = singles + 2 * active
    binary = 1
    if weight > 2 * unique_terms:
        binary = 2**weight // sum(comb(weight, i) for i in range(unique_terms + 1))
    fixed_support = comb(zeros, active) * binary

    free_blocks = min(unique_terms, active)
    free_signs = min(singles, unique_terms - free_blocks)
    marks = comb(zeros, active - free_blocks) * 4**(active - free_blocks)
    by_marking = marks * 2**(singles - free_signs) // comb(active, free_blocks)
    return min(fixed_support, by_marking)


def degree_cap(order, size, completion_cap, unique_terms=4, low_cutoff=5, distance=31):
    """Return the low-weight charge and charges by number of double imbalances."""
    blocks = order // 4
    low_weight = 0
    for weight in range(size % 2, min(low_cutoff, size) + 1, 2):
        pins = max(0, weight - unique_terms)
        count = comb(order // 2, pins) * 2**pins // comb(weight, pins)
        low_weight += count * completion_cap((size - weight) // 2)

    by_doubles = []
    for doubles in range(min(blocks, size // 2) + 1):
        total = 0
        for singles in range(size % 2, min(blocks - doubles, size - 2*doubles) + 1, 2):
            orientations = signed_imbalance_cap(blocks, doubles, singles, distance)
            pairs = (size - 2*doubles - singles) // 2
            for triples in range(min(singles, pairs) + 1):
                zero_blocks = blocks - doubles - singles
                for full in range(min(zero_blocks, (pairs - triples) // 2) + 1):
                    active = pairs - triples - 2*full
                    if active > zero_blocks - full or singles + 2*active <= low_cutoff:
                        continue
                    labels = comb(singles, triples) * comb(zero_blocks, full)
                    total += orientations * labels * phase_cap(zero_blocks - full, active, singles, unique_terms)
        by_doubles.append(total)
    return low_weight, by_doubles


def check_small_domain():
    order, prime = 16, 998244353
    root = pow(3, (prime - 1) // order, prime)
    powers = root_table(order, root, prime)
    verify_short_sums(order, [(prime, root)])
    # Enumerate every unreduced multiset, separately from the orbit method.
    reduced_by_sum = {}
    for size in range(6):
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
    sums_products = {}
    for size in range(5):
        counts = Counter()
        joint = Counter()
        for sites in combinations(range(order // 2), size):
            value = sum(powers[2*j] for j in sites) % prime
            counts[value] += 1
            joint[value, sum(sites) % (order // 2)] += 1
        sums[size] = max(counts.values())
        sums_products[size] = max(joint.values())
    blocks = order // 4
    for size in (7, 8, 9):
        counts = Counter()
        product_counts = Counter()
        phases = Counter()
        for sites in combinations(range(order), size):
            sites = set(sites)
            first = sum(powers[j] for j in sites) % prime
            second = sum(powers[2*j % order] for j in sites) % prime
            counts[first, second] += 1
            product_counts[first, second, sum(sites) % order] += 1
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
                if weight > 7 and phases[key] > phase_cap(zeros, active, singles, 5):
                    raise ArithmeticError(("five-term phase count", key, phases[key]))
        low, charges = degree_cap(order, size, sums.__getitem__)
        if max(counts.values()) > low + sum(charges):
            raise ArithmeticError((size, max(counts.values()), low, charges))
        low, charges = degree_cap(order, size, sums_products.__getitem__,
                                  unique_terms=5, low_cutoff=7, distance=32)
        if max(product_counts.values()) > low + sum(charges):
            raise ArithmeticError(("five-term product cap", size, low, charges))
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

    # The independent GMP probe verifies uniqueness through five terms at both primes.
    low, charges = degree_cap(256, 19, first_sum_product_cap, unique_terms=5, low_cutoff=7)
    degree19 = low + sum(charges)
    if degree19 != 122575042:
        raise ArithmeticError(("five-term fixed-product cap", low, charges, degree19))
    for prime in PRIMES:
        for order, low_degree, slack in ((128, 12, 9), (256, 23, 17)):
            for m in range(low_degree, order + 1):
                if unlifted_orders(order, m, m - slack, prime):
                    raise ArithmeticError(("incomplete integral lift", prime, order, m))
        if unlifted_orders(256, 22, 5, prime) != [128]:
            raise ArithmeticError(("degree 22 orientation", prime))
    tail128 = sum(full_lift_cap(128, m, m - 9) for m in range(12, 129))
    order128 = first_sum_product_cap(10) + first_sum_product_cap(11) + tail128
    tail256 = sum(full_lift_cap(256, m, m - 17) for m in range(23, 257))
    degree20 = mixed_cap(20, first_sum_product_cap)
    degree21 = mixed_cap(21, first_sum_product_cap)
    degree22 = max(first_sum_product_cap(q) for q in range(12))
    order256 = degree19 + degree20 + degree21 + degree22 + tail256
    # The fresh-coordinate verifier certifies this cap at 20h-1 agreements.
    degree18 = 721759140
    combined = degree18 + order256 + order128
    if (tail128, order128, degree20, degree21, degree22, tail256, combined) != (
            5324, 600989, 17431579, 200070257, 357399, 6076, 1062800482):
        raise ArithmeticError(("combined fixed-product cap", order128, order256, combined))
    print("fixed-product degree 19 low and imbalance charges:", low, charges)
    print("fixed-product 256 degrees 19, 20, 21, 22, and 23..256:",
          degree19, degree20, degree21, degree22, tail256)
    print("fixed-product 128 degrees 10, 11, and 12..128:",
          first_sum_product_cap(10), first_sum_product_cap(11), tail128)
    print("order-256 degree 18 up to eight unpaired, plus both higher-degree ranges:",
          combined, "headroom", 2**30 - combined)
    # The same incidence count holds at a variable threshold. In an over-budget
    # union, every candidate beyond the higher-degree caps comes from degree 18.
    h = 2**22
    fresh_matches_per_site = 2830428
    if 255 * fresh_matches_per_site != degree18:
        raise ArithmeticError("degree-18 fresh match cap")
    safe_agreements = []
    for budget in (2**30, 2**31):
        required_degree18 = budget + 1 - order128 - order256
        if required_degree18 <= fresh_matches_per_site:
            raise ArithmeticError("incidence envelope is not increasing in common roots")
        safe_agreements.append(19 * h + (255 * h + 1) * fresh_matches_per_site
                               // required_degree18)
    if safe_agreements != [83823446, 81367598]:
        raise ArithmeticError(("combined threshold", safe_agreements))
    print("combined family within budget at agreements >=", safe_agreements)


if __name__ == "__main__":
    main()
