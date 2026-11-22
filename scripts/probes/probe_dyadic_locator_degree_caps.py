"""Check fixed-coefficient locator population caps on the two designated smooth fields."""

from collections import Counter
from itertools import combinations
from math import comb


PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)


def unlifted_orders(order, size, moments, prime):
    """Orders at which the integral determinant bound permits a nonzero difference."""
    missing = []
    for valuation in range(moments.bit_length()):
        conductor = order >> valuation
        roots = ((moments >> valuation) + 1) // 2
        folded_energy = 4 * (order // conductor) * min(size, order - size)
        if folded_energy ** (conductor // 2) >= prime ** (2 * roots):
            missing.append(conductor)
    return missing


def signed_support_cap(length, weight, distance):
    """Shorten on marked signed coordinates, then apply the squared-distance bound."""
    bounds = []
    for fixed in range(weight + 1):
        gap = distance - 2 * (weight - fixed)
        if gap > 0:
            marked = 2**fixed * comb(length, fixed)
            bounds.append(marked * (distance // gap) // comb(weight, fixed))
    return min(bounds)


def first_sum_cap(size):
    """Number of subsets of this size on the order-128 group with prescribed sum."""
    return min(comb(128, size), (31 // (31 - 2 * size)) * comb(64, size // 2))


def mixed_cap(size):
    total = 0
    for weight in range(size % 2, size + 1, 2):
        pairs = (size - weight) // 2
        total += signed_support_cap(128, weight, 31) * first_sum_cap(pairs)
    return total


def full_lift_cap(order, size, moments):
    block = 1 << moments.bit_length()
    return comb(order // block, min(size, order - size) // block)


def check_small_fields():
    checks = 0
    for order, prime in ((8, 17), (8, 41), (16, 97), (16, 65537)):
        root = next(x for x in range(2, prime) if pow(x, order // 2, prime) == prime - 1)
        for size in range(2, order):
            for moments in range(1, min(size, 4)):
                if unlifted_orders(order, size, moments, prime):
                    continue
                powers = [tuple(pow(root, j*k, prime) for k in range(1, moments+1))
                          for j in range(order)]
                counts = Counter(tuple(sum(powers[j][k] for j in sites) % prime
                                       for k in range(moments))
                                 for sites in combinations(range(order), size))
                if max(counts.values()) > full_lift_cap(order, size, moments):
                    raise ArithmeticError((order, prime, size, moments))
                checks += 1
    return checks


def main():
    print("small exhaustive fixed-moment controls:", check_small_fields())
    for prime in PRIMES:
        if 30**32 >= prime or prime % 256 != 1:
            raise ArithmeticError("incorrect prime bound or quotient order")
        for order, start in ((128, 10), (256, 20)):
            caps = {}
            for size in range(start, order + 1):
                moments = size - (order // 16 + 1)
                missing = unlifted_orders(order, size, moments, prime)
                if not missing:
                    cap = full_lift_cap(order, size, moments)
                elif order == 128 and size in (10, 11) and missing == [128]:
                    cap = first_sum_cap(size)
                elif order == 256 and size in (20, 21) and missing == [256, 128]:
                    cap = mixed_cap(size)
                elif order == 256 and size == 22 and missing == [128]:
                    cap = max(first_sum_cap(pairs) for pairs in range(12))
                else:
                    raise ArithmeticError((order, size, missing))
                caps[size] = cap
            if max(caps.values()) >= 2**30 or sum(caps.values()) >= 2**30:
                raise ArithmeticError("upper bounds exceed the first designated budget")
            print(f"prime={prime} order={order} degrees={start}..{order} "
                  f"max={max(caps.values())} sum={sum(caps.values())}")
    print("degree 20, 21 shortened caps:", mixed_cap(20), mixed_cap(21))


if __name__ == "__main__":
    main()
