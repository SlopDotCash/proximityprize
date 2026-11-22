"""Check product-conditioned dyadic norm bounds and the named-field locator unions."""

from collections import defaultdict
from itertools import combinations

from probe_dyadic_locator_degree19 import degree_cap
from probe_dyadic_locator_degree_caps import (
    PRIMES, first_sum_product_cap, full_lift_cap, mixed_cap, product_layer_cap, unlifted_orders,
)
from probe_dyadic_locator_quotient_classification import (
    AGREEMENTS, EIGHT_UNPAIRED_SIGNATURES, LENGTH, SIGNATURES_128, SIGNATURES_256, small_quotient,
)
from probe_locator_baseline_occupancy import list_cap
from probe_order16_weight13_spectrum import determinant_norm


def check_small_determinants():
    # Compare actual integer determinants for every equal-size, equal-product
    # pair on the order-eight group. Both conductors have examples of norm 4.
    for conductor in (4, 8):
        half = conductor // 2
        checked = 0
        found_four = False
        for weight in range(9):
            by_product = defaultdict(list)
            for support in combinations(range(8), weight):
                by_product[sum(support) % 8].append(support)
            for supports in by_product.values():
                for left, right in combinations(supports, 2):
                    folded = [0] * half
                    for sign, support in ((1, left), (-1, right)):
                        for j in support:
                            folded[j % half] += sign * (-1)**(j // half)
                    norm = abs(determinant_norm(folded))
                    if norm % 4:
                        raise ArithmeticError(("norm lacks factor four", conductor, left, right))
                    checked += 1
                    found_four |= norm == 4
        if checked != 682 or not found_four:
            raise ArithmeticError(("incomplete small norm check", conductor, checked))
        # Equal cardinality alone permits norm 2: the two singletons 1 and X.
        if abs(determinant_norm([1, -1] + [0] * (half - 2))) != 2:
            raise ArithmeticError(("missing different-product control", conductor))


def even_distance(prime, conductor, prime_factors):
    """Least even energy at which Hadamard permits a nonzero multiple of 4 p^c."""
    distance = 2
    while distance ** (conductor // 4) < 4 * prime**prime_factors:
        distance += 2
    return distance


def higher_caps(prime):
    half_distance = even_distance(prime, 128, 1)
    primitive_distance = even_distance(prime, 256, 2)

    def complete(q):
        return first_sum_product_cap(q, distance=half_distance)

    # Degree 19 uses the second moment at conductor 128 for imbalance
    # vectors and five-term sum uniqueness at the primitive conductor.
    low, charges = degree_cap(256, 19, complete, unique_terms=5, low_cutoff=7,
                              distance=half_distance)
    # Degrees 20 and 21 have primitive moments at frequencies 1 and 3,
    # plus the second moment for the labels of the remaining full pairs.
    middle = [mixed_cap(m, complete, distance=primitive_distance) for m in (20, 21)]
    if unlifted_orders(256, 22, 5, prime) != [128]:
        raise ArithmeticError("degree 22 lacks its integral primitive lift")
    for order, start in ((128, 12), (256, 23)):
        for m in range(start, order + 1):
            if unlifted_orders(order, m, m - order // 16 - 1, prime):
                raise ArithmeticError(("incomplete tail lift", order, m))
    tail256 = sum(full_lift_cap(256, m, m - 17) for m in range(23, 257))
    tail128 = sum(full_lift_cap(128, m, m - 9) for m in range(12, 129))
    high128 = complete(10) + complete(11) + tail128
    high256 = [low + sum(charges), *middle, max(complete(q) for q in range(12)), tail256]
    return (half_distance, primitive_distance), high128, high256


def occupancy_caps(agreement):
    low128 = [list_cap(128, m, LENGTH // 128, agreement, cap)
              for m, cap in enumerate(SIGNATURES_128)]
    low256 = [list_cap(256, m, LENGTH // 256, agreement, cap)
              for m, cap in enumerate(SIGNATURES_256)]
    degree18 = list_cap(256, 18, LENGTH // 256, agreement, EIGHT_UNPAIRED_SIGNATURES)
    return low128, low256, degree18


def main():
    check_small_determinants()
    tiny = sum(product_layer_cap(order, size) for order in (1, 2, 4, 8)
               for size in range(order + 1))
    small = tiny + sum(small_quotient(order) for order in (16, 32, 64))
    low128, low256, degree18 = occupancy_caps(AGREEMENTS)
    if (small, sum(low128), sum(low256[:9]), low256[9], degree18) != (
            165240, 13161160, 48151877, 1332411487, 617033304):
        raise ArithmeticError(("occupancy inputs", small, low128, low256, degree18))
    for i, prime in enumerate(PRIMES):
        distances, high128, high256 = higher_caps(prime)
        total = small + sum(low128) + high128 + sum(low256[:9 + i]) + degree18 + sum(high256)
        expected256 = ([48952114, 9150513, 103415663, 238266, 6076],
                       [48952114, 961555, 7480691, 238266, 6076])[i]
        if (distances, high128, high256, total) != (
                (34, 32 + 2*i), 481856, expected256, (840756069, 2069043626)[i]):
            raise ArithmeticError(("combined prime-specific cap", distances, high128, high256, total))
        print("field", i + 1, "distances at 128, 256:", distances, "higher caps:", high128, high256)
        print("union through low order-256 degree", 8 + i, "cap:", total,
              "headroom:", 2**(30 + i) - total)
        threshold = (82747292, 83482060)[i]
        adjacent = []
        for t in (threshold - 1, threshold):
            a, b, c = occupancy_caps(t)
            adjacent.append(small + high128 + sum(high256) + sum(a) + sum(b[:9+i]) + c)
        if not adjacent[1] <= 2**(30 + i) < adjacent[0]:
            raise ArithmeticError(("agreement floor", threshold, adjacent))
        print("safe at", threshold, "agreements; adjacent envelope values:", adjacent)


if __name__ == "__main__":
    main()
