#!/usr/bin/env python3
"""Exact scanner for the order-eight dimension-two field-stability boundary.

The scanner implements the integer-threshold MCA event for monomial pencils on the
order-eight subgroup of every prime field ``F_p`` with ``p = 1 mod 8`` and
``17 <= p <= 10000``.  It checks two quantities:

* the ceiling stack ``(x^3, x^2)`` at agreement threshold three;
* the maximum over all 64 monomial pencils at agreement threshold four.

All arithmetic is exact Python integer arithmetic.  There are no third-party
dependencies and every asserted result fails closed.
"""

from itertools import combinations
from math import isqrt

LIMIT = 10_000
EXPECTED_MAXIMIZERS = ((4, 3), (4, 7), (5, 2), (5, 6))


def primes_one_mod_eight(limit: int) -> list[int]:
    """Return all primes congruent to one modulo eight in ``[17, limit]``."""
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            count = (limit - start) // divisor + 1
            sieve[start : limit + 1 : divisor] = b"\x00" * count
    return [p for p in range(17, limit + 1) if sieve[p] and p % 8 == 1]


def order_eight_generator(p: int) -> int:
    """Find an element of exact order eight in ``F_p``."""
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // 8, p)
        if pow(generator, 4, p) == p - 1:
            assert pow(generator, 8, p) == 1
            return generator
    raise AssertionError(f"no order-eight generator found modulo {p}")


def scan_prime(p: int) -> tuple[int, int, tuple[tuple[int, int], ...]]:
    """Return the ceiling count, below-ceiling maximum, and all maximizers."""
    generator = order_eight_generator(p)
    domain = [pow(generator, exponent, p) for exponent in range(8)]
    assert len(set(domain)) == 8

    def is_affine_on(values: list[int], indices: list[int]) -> bool:
        first, second = indices[:2]
        slope = (
            (values[second] - values[first])
            * pow(domain[second] - domain[first], -1, p)
        ) % p
        intercept = (values[first] - slope * domain[first]) % p
        return all(
            (intercept + slope * domain[index] - values[index]) % p == 0
            for index in indices
        )

    def bad_scalars(first_exp: int, second_exp: int, threshold: int) -> set[int]:
        first_word = [pow(x, first_exp, p) for x in domain]
        second_word = [pow(x, second_exp, p) for x in domain]
        candidates: set[int] = set()

        # Eliminate the affine codeword coefficients from each three-point system.
        # Every MCA witness of size at least three contains such a determining triple.
        for first, second, third in combinations(range(8), 3):
            a11 = (domain[second] - domain[first]) % p
            a12 = (-(second_word[second] - second_word[first])) % p
            a21 = (domain[third] - domain[first]) % p
            a22 = (-(second_word[third] - second_word[first])) % p
            b1 = (first_word[second] - first_word[first]) % p
            b2 = (first_word[third] - first_word[first]) % p
            determinant = (a11 * a22 - a12 * a21) % p
            if determinant:
                gamma = (a11 * b2 - b1 * a21) * pow(determinant, -1, p) % p
                candidates.add(gamma)

        bad: set[int] = set()
        for gamma in candidates:
            pencil = [
                (first_word[index] + gamma * second_word[index]) % p
                for index in range(8)
            ]
            witnesses: set[tuple[int, ...]] = set()
            for first, second in combinations(range(8), 2):
                slope = (
                    (pencil[second] - pencil[first])
                    * pow(domain[second] - domain[first], -1, p)
                ) % p
                intercept = (pencil[first] - slope * domain[first]) % p
                witness = tuple(
                    index
                    for index in range(8)
                    if (intercept + slope * domain[index] - pencil[index]) % p == 0
                )
                witnesses.add(witness)

            # This is the existential witness and `pairJointAgreesOn` exclusion in
            # `mcaEventNat`; inspect every distinct affine witness, not only a largest one.
            if any(
                len(witness) >= threshold
                and not (
                    is_affine_on(first_word, list(witness))
                    and is_affine_on(second_word, list(witness))
                )
                for witness in witnesses
            ):
                bad.add(gamma)
        return bad

    ceiling_count = len(bad_scalars(3, 2, 3))
    pencil_counts = {
        (first_exp, second_exp): len(bad_scalars(first_exp, second_exp, 4))
        for first_exp in range(8)
        for second_exp in range(8)
    }
    maximum = max(pencil_counts.values())
    maximizers = tuple(pair for pair, count in pencil_counts.items() if count == maximum)
    return ceiling_count, maximum, maximizers


def main() -> None:
    primes = primes_one_mod_eight(LIMIT)
    assert primes[0] == 17
    results = {p: scan_prime(p) for p in primes}

    assert results[17] == (16, 9, EXPECTED_MAXIMIZERS)
    stable_primes = primes[1:]
    assert stable_primes[0] == 41
    assert all(results[p] == (40, 9, EXPECTED_MAXIMIZERS) for p in stable_primes)

    print("G328 exact order-eight dimension-two scan")
    print(f"tested_primes={len(primes)} range={primes[0]}..{primes[-1]}")
    print(f"exception p=17 ceiling={results[17][0]} below_max={results[17][1]}")
    print(
        "stable_range "
        f"p={stable_primes[0]}..{stable_primes[-1]} "
        f"count={len(stable_primes)} ceiling=40 below_max=9"
    )
    print(f"maximizers={EXPECTED_MAXIMIZERS}")
    print("PASS: universal field-independence is false; the tested stable range starts at p=41")


if __name__ == "__main__":
    main()
