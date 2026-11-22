"""Count the union of the indicated fixed-numerator locator families on both named fields."""

from collections import Counter
from itertools import combinations
from math import prod

from probe_dyadic_locator_degree19 import degree_cap
from probe_dyadic_locator_degree_caps import (
    PRIMES, first_sum_product_cap, full_lift_cap, mixed_cap, product_layer_cap, unlifted_orders,
)


LENGTH = 2**30
AGREEMENTS = 20 * (LENGTH // 256) - 1
# Exact signature counts and consequences of their product-conditioned energies
# from probe_antipodal_locator_fresh_energy.cpp. Entry m bounds the number of
# m-subsets of nonidentity quotient roots with a specified product and locator.
SIGNATURES_128 = (1, 1, 1, 2, 6, 57, 1206, 19022, 160036)
SIGNATURES_256 = (1, 1, 1, 2, 6, 108, 4590, 155998, 2562572, 72606206)
EIGHT_UNPAIRED_SIGNATURES = 2830428


def small_quotient(order):
    """Every degree on the order-16, -32 and -64 quotients."""
    total = 0
    for m in range(order + 1):
        moments = m - order // 16 - 1
        if moments <= 0:
            total += product_layer_cap(order, m)
        else:
            for prime in PRIMES:
                if unlifted_orders(order, m, moments, prime):
                    raise ArithmeticError(("unlifted small quotient", order, m, prime))
            total += full_lift_cap(order, m, moments)
    return total


def even_completion(size):
    return first_sum_product_cap(size, distance=32)


def higher_degrees():
    for prime in PRIMES:
        if prime <= 30**32:
            raise ArithmeticError("the named field lacks the signed-vector separation")
        for order, start in ((128, 12), (256, 23)):
            for m in range(start, order + 1):
                if unlifted_orders(order, m, m - order // 16 - 1, prime):
                    raise ArithmeticError(("missing higher-degree lift", order, m, prime))
        if unlifted_orders(256, 22, 5, prime) != [128]:
            raise ArithmeticError(("degree 22 orientation", prime))
    low, charges = degree_cap(256, 19, even_completion, unique_terms=5, low_cutoff=7,
                              distance=32)
    order256 = (low + sum(charges), mixed_cap(20, even_completion, distance=32),
                mixed_cap(21, even_completion, distance=32),
                max(even_completion(q) for q in range(12)),
                sum(full_lift_cap(256, m, m - 17) for m in range(23, 257)))
    order128 = sum(even_completion(m) for m in (10, 11)) + sum(
        full_lift_cap(128, m, m - 9) for m in range(12, 129))
    return order128, order256


def in_ball(order, size, fresh_per_site, agreements, length=LENGTH):
    """A degree-m candidate has at most mh ordinary agreements off the common zeros."""
    h = length // order
    common_zeros = h - 1
    extra = agreements - size * h - common_zeros
    raw = product_layer_cap(order, size)
    if extra <= 0:
        return raw
    # The incidence ratio is largest when exactly size*h eligible sites
    # carry the baseline value, leaving the other sites for fresh matches.
    return min(raw, (length - common_zeros - size * h) * fresh_per_site // extra)


def check_small_balls():
    # All fixed-product locator subsets on the order-eight quotient of F_17^*.
    # Centers include an entire candidate, the common baseline, and mixed centers.
    prime, order, length = 17, 8, 16
    domain = range(1, prime)
    fibers = [x*x % prime for x in domain]
    quotient = sorted(set(fibers))
    for size in range(5):
        supports = list(combinations(quotient, size))
        signatures = Counter((prod(s) % prime, prod(1-z for z in s) % prime)
                             for s in supports if 1 not in s)
        for constant in {prod(s) % prime for s in supports}:
            group = [s for s in supports if prod(s) % prime == constant]
            for root in (0, 1):
                # A common multiplier with zero or one root on the domain.
                scaled = [(x - root) * pow(y, -1, prime) % prime
                          for x, y in zip(domain, fibers)]
                baseline = [u * (y**size + (-1)**size * constant if size else 1) % prime
                            for u, y in zip(scaled, fibers)]
                words = [tuple((v - u * prod(y-z for z in support)) % prime
                               for u, v, y in zip(scaled, baseline, fibers))
                         for support in group]
                centers = [baseline, *words, [v if x % 3 == 0 else w
                                               for x, v, w in zip(domain, baseline, words[-1])]]
                for center in centers:
                    matches = [sum(v == w for v, w in zip(word, center)) for word in words]
                    for t in range(length + 1):
                        cap = in_ball(order, size, max(signatures.values()), t, length)
                        if sum(a >= t for a in matches) > cap:
                            raise ArithmeticError(("small received ball", size, constant, root, t))


def main():
    check_small_balls()
    tiny = [sum(product_layer_cap(order, m) for m in range(order + 1))
            for order in (1, 2, 4, 8)]
    small = [small_quotient(order) for order in (16, 32, 64)]
    order128, high256 = higher_degrees()
    low128 = [in_ball(128, m, cap, AGREEMENTS) for m, cap in enumerate(SIGNATURES_128)]
    degree18 = in_ball(256, 18, EIGHT_UNPAIRED_SIGNATURES, AGREEMENTS)
    if (tiny, small, order128, high256, low128, degree18) != (
            [2, 3, 7, 67], [45, 360, 164756], 600989, (87921070, 9190224, 103455374, 357399, 6076),
            [1, 1, 17, 41, 147, 1738, 48642, 1141320, 19044284], 670811436):
        raise ArithmeticError((tiny, small, order128, high256, low128, degree18))
    print("all degrees at orders 1, 2, 4, 8, 16, 32, 64:", tiny + small)
    print("order 128 degrees 0..8, followed by 10..128:", low128, order128)
    print("order 256 degree 18 up to eight unpaired and degrees 19 through 256:",
          degree18, high256)
    base = sum(tiny) + sum(small) + sum(low128) + order128 + sum(high256)
    low256 = [in_ball(256, m, cap, AGREEMENTS) for m, cap in enumerate(SIGNATURES_256)]
    # By unique five-term sums, weights 2, 4 and 6 are pairwise exclusive
    # at a fixed first sum; they admit at most 1, 1 and 42 orientations.
    nonzero_low_weights = max(SIGNATURES_128[8], SIGNATURES_128[7],
                              (256 // 6) * SIGNATURES_128[6])
    second_degree18 = in_ball(256, 18, nonzero_low_weights, AGREEMENTS)
    combined = base + degree18 + sum(low256[:9])
    second = base + second_degree18 + sum(low256)
    if (low256, combined, second_degree18, second) != (
            [1, 1, 14, 31, 100, 1928, 87916, 3223958, 57541389, 1786112669],
            953599337, 37928532, 2106829102):
        raise ArithmeticError(("union", low256, combined, second_degree18, second))
    print("order 256 degrees 0..9:", low256)
    print("combined cap through order-256 degree 8:", combined, "headroom:", 2**30 - combined)
    print("second-budget cap through order-256 degree 9 with 2, 4 or 6 unpaired in degree 18:",
          second, "headroom:", 2**31 - second)
    # Evaluate the same monotone envelope on the two neighboring integers.
    fixed = sum(tiny) + sum(small) + order128 + sum(high256)
    for budget, max_degree, fresh18, threshold in (
            (2**30, 8, EIGHT_UNPAIRED_SIGNATURES, 83259878),
            (2**31, 8, EIGHT_UNPAIRED_SIGNATURES, 81211130),
            (2**31, 9, nonzero_low_weights, 83185696)):
        caps = []
        for t in (threshold - 1, threshold):
            bound = fixed + in_ball(256, 18, fresh18, t)
            bound += sum(in_ball(128, m, c, t) for m, c in enumerate(SIGNATURES_128))
            bound += sum(in_ball(256, m, c, t)
                         for m, c in enumerate(SIGNATURES_256[:max_degree + 1]))
            caps.append(bound)
        if not caps[1] <= budget < caps[0]:
            raise ArithmeticError(("threshold crossing", budget, threshold, caps))
        print("budget", budget, "through degree", max_degree, "safe at", threshold,
              "agreements; adjacent calculated bounds", caps)


if __name__ == "__main__":
    main()
