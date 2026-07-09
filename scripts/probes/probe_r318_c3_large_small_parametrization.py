#!/usr/bin/env python3
"""#466 R318: exact raw parametrization of the c=3 small collision stratum.

For an oriented primitive n-th root zeta satisfying zeta^h = 3 with
k = n/2 - h, R317 proves the field identity

    zeta^s + zeta^(s+t) + zeta^(s+k)
      = zeta^(s+t) - 2 zeta^(s+k).

This probe checks the newly observed sharp nondegenerate parameter slice.  Delete
the seven offsets

    {0, k, m, m+k, h+1, m+h, m+h+1},  m = n/2.

For every remaining pair (s,t), the two char-zero shadow vectors have exact
histogram weights (6,3), evaluate to the same field value, and their field
centers are pairwise distinct.  Thus the slice has exactly n(n-7) small
fibers, matching the complete R310 c=3 histogram without using the middle
stratum.
"""

from __future__ import annotations

import argparse
from collections import Counter

from probe_r305_complete_census import build_n3
from probe_r307_binomial_norm_depth3 import order_n_element


CASES = (
    (32, 21523361),
    (64, 926510094425921),
    (128, 1716841910146256242328924544641),
)


def orient_c3_root(modulus: int, prime: int) -> tuple[int, int, int, int]:
    """Find an odd-power orientation with zeta^h = 3 and 0 < h < n/2."""
    base_root = order_n_element(prime, modulus)
    half_order = modulus // 2
    for orientation_exponent in range(1, modulus, 2):
        oriented_root = pow(base_root, orientation_exponent, prime)
        for relation_exponent in range(1, half_order):
            if pow(oriented_root, relation_exponent, prime) == 3:
                return (
                    oriented_root,
                    relation_exponent,
                    half_order - relation_exponent,
                    orientation_exponent,
                )
    raise ValueError(f"no signed c=3 orientation for n={modulus}, p={prime}")


def shadow_of_triple(modulus: int, triple: tuple[int, int, int]) -> tuple[int, ...]:
    """Return the signed dyadic char-zero shadow of three root indices."""
    half_order = modulus // 2
    shadow = [0] * half_order
    for exponent in triple:
        if exponent >= half_order:
            shadow[exponent - half_order] -= 1
        else:
            shadow[exponent] += 1
    return tuple(shadow)


def evaluate_shadow(
    shadow: tuple[int, ...], powers: list[int], prime: int
) -> int:
    return sum(
        coefficient * powers[index]
        for index, coefficient in enumerate(shadow)
    ) % prime


def verify_case(modulus: int, prime: int) -> bool:
    half_order = modulus // 2
    oriented_root, relation_exponent, complement_exponent, orientation_exponent = orient_c3_root(
        modulus, prime
    )
    keys, counts = build_n3(modulus)
    shadow_histogram = {
        tuple(map(int, row)): int(count)
        for row, count in zip(keys, counts)
    }
    powers = [pow(oriented_root, exponent, prime) for exponent in range(half_order)]
    excluded_offsets = {
        0,
        complement_exponent,
        half_order,
        (half_order + complement_exponent) % modulus,
        (relation_exponent + 1) % modulus,
        (half_order + relation_exponent) % modulus,
        (half_order + relation_exponent + 1) % modulus,
    }
    expected_count = modulus * (modulus - 7)
    parameter_count = 0
    centers: set[int] = set()
    shadow_pairs: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    failures: Counter[tuple[int, int, bool, bool]] = Counter()

    for shift in range(modulus):
        for offset in range(modulus):
            if offset in excluded_offsets:
                continue
            left_shadow = shadow_of_triple(
                modulus,
                (shift, (shift + offset) % modulus, (shift + complement_exponent) % modulus),
            )
            right_shadow = shadow_of_triple(
                modulus,
                (
                    (shift + offset) % modulus,
                    (shift + complement_exponent + half_order) % modulus,
                    (shift + complement_exponent + half_order) % modulus,
                ),
            )
            left_value = evaluate_shadow(left_shadow, powers, prime)
            right_value = evaluate_shadow(right_shadow, powers, prime)
            signature = (
                shadow_histogram[left_shadow],
                shadow_histogram[right_shadow],
                left_value == right_value,
                left_shadow == right_shadow,
            )
            if signature != (6, 3, True, False):
                failures[signature] += 1
            parameter_count += 1
            centers.add(left_value)
            shadow_pairs.add((left_shadow, right_shadow))

    passed = (
        len(excluded_offsets) == 7
        and parameter_count == expected_count
        and not failures
        and len(centers) == expected_count
        and len(shadow_pairs) == expected_count
    )
    print(
        f"n={modulus} p={prime} orientation={orientation_exponent} "
        f"h={relation_exponent} k={complement_exponent}"
    )
    print(f"  excluded={sorted(excluded_offsets)}")
    print(
        f"  parameters={parameter_count} centers={len(centers)} "
        f"shadow_pairs={len(shadow_pairs)} expected={expected_count}"
    )
    print(f"  failures={dict(failures)}")
    print(f"  seven-exception small-family law: {'PASS' if passed else 'FAIL'}")
    return passed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int)
    parser.add_argument("--p", type=int)
    arguments = parser.parse_args()
    if (arguments.n is None) != (arguments.p is None):
        parser.error("pass --n and --p together")
    cases = CASES if arguments.n is None else ((arguments.n, arguments.p),)
    return 0 if all(verify_case(modulus, prime) for modulus, prime in cases) else 1


if __name__ == "__main__":
    raise SystemExit(main())
