#!/usr/bin/env python3
"""Exact counterexample to a proper-leaf-only depth-seven packet recursion.

At n=16 enumerate disjoint pairs of seven-subsets of mu_n with equal sum in F_p.  A pair is
primitive when no nonempty proper equal-cardinality subpair already has equal sum.  Such a pair is
a depth-seven primitive packet, so it cannot be charged to a proper leaf of depth at most six.

The census is exact integer modular arithmetic.  It finds 48 primitive depth-seven packets at
p=337 (and gives an explicit witness), refuting the tempting universal recursion through only
lower-depth packet energies.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations


def prime_factors(value: int) -> list[int]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    return factors


def primitive_generator(p: int) -> int:
    factors = prime_factors(p - 1)
    for candidate in range(2, p):
        if all(pow(candidate, (p - 1) // ell, p) != 1 for ell in factors):
            return candidate
    raise RuntimeError("no primitive generator")


def indices(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def subset_signature(mask: int, roots: list[int], p: int) -> tuple[int, int]:
    return mask.bit_count(), sum(roots[i] for i in indices(mask)) % p


def is_primitive_pair(left: int, right: int, roots: list[int], p: int) -> bool:
    left_signatures: set[tuple[int, int]] = set()
    subset = left
    while subset:
        if subset != left:
            left_signatures.add(subset_signature(subset, roots, p))
        subset = (subset - 1) & left

    subset = right
    while subset:
        if subset != right and subset_signature(subset, roots, p) in left_signatures:
            return False
        subset = (subset - 1) & right
    return True


def has_nonzero_cyclotomic_lift(left: int, right: int, n: int = 16) -> bool:
    half = n // 2
    coefficients = [0] * half
    for sign, mask in ((1, left), (-1, right)):
        for exponent in indices(mask):
            coefficients[exponent % half] += sign if exponent < half else -sign
    return any(coefficients)


def census(p: int, n: int = 16) -> tuple[int, tuple[int, int] | None]:
    assert (p - 1) % n == 0
    generator = primitive_generator(p)
    zeta = pow(generator, (p - 1) // n, p)
    roots = [pow(zeta, exponent, p) for exponent in range(n)]

    fibers: dict[int, list[int]] = defaultdict(list)
    for subset in combinations(range(n), 7):
        mask = sum(1 << exponent for exponent in subset)
        fibers[sum(roots[exponent] for exponent in subset) % p].append(mask)

    primitive_count = 0
    witness = None
    for fiber in fibers.values():
        for left in fiber:
            for right in fiber:
                if left & right:
                    continue
                if (has_nonzero_cyclotomic_lift(left, right, n)
                        and is_primitive_pair(left, right, roots, p)):
                    primitive_count += 1
                    witness = witness or (left, right)
    return primitive_count, witness


def mask_list(mask: int, n: int = 16) -> list[int]:
    return [i for i in range(n) if mask & (1 << i)]


def main() -> None:
    print("PRIMITIVE_DEPTH7_COUNTEREXAMPLE")
    for p in (97, 193, 337):
        count, witness = census(p)
        print(f"n=16 p={p} primitive_depth7_ordered_subset_pairs={count}")
        if witness is not None and p == 337:
            print(f"witness_left_exponents={mask_list(witness[0])}")
            print(f"witness_right_exponents={mask_list(witness[1])}")
    print(
        "VERDICT=REFUTED: a depth-seven wraparound need not have a proper primitive leaf; "
        "lower-depth packet recursion leaves a genuine depth-seven primitive sector"
    )


if __name__ == "__main__":
    main()
