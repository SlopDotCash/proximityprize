#!/usr/bin/env python3
"""Verify the arithmetic contract for the G139 n=2^30 Phi artifact.

This is a lightweight companion to the retained chunk verifier.  It checks the
small arithmetic facts that connect the public n=2^30 result JSON to the Lean
bridge:

* p is prime, via a recursive Pocklington certificate.
* p - 1 = n * q, with the recorded complete factorization.
* g has exact order n = 2^30.
* if a result JSON is supplied, its half-window and collision fields match the
  expected production-row certificate values.

It intentionally does not read the 128 retained chunk binaries; that remains
the job of the release verifier.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from math import gcd, prod
from pathlib import Path


N = 1 << 30
P = 365375409332725729550921208179070755196377235457
Q = 340282366920938463463374607431768211719
G = 26841566604131443990650262696798142924116991820
DOMAIN_SIZE = N // 2
PHI_IMAGE_SHA256 = "47e60af06c23828d8b4353255b0dca55a4f8b7580692778ec03f6f3f8fabbc6a"
SORTED_RECORD_STREAM_SHA256 = "6e084eb8a7fa66d7e63d8f3855649764ad06a7e2de4dbe4145f34337c372b6f5"

Q_FACTORS = (3, 23, 37, 3251, 11633, 31531, 111774359022899775527551)
LARGE_Q_FACTOR = 111774359022899775527551
LARGE_Q_FACTOR_FACTORS = (2, 3, 5, 5, 23, 2141, 15132351674065319)

P_POCKLINGTON_WITNESSES = {
    2: 5,
    3: 2,
    23: 2,
    37: 2,
    3251: 2,
    11633: 2,
    31531: 2,
    LARGE_Q_FACTOR: 2,
}

LARGE_Q_FACTOR_POCKLINGTON_WITNESSES = {
    2: 3,
    3: 7,
    5: 2,
    23: 2,
    2141: 2,
    15132351674065319: 2,
}


def is_prime_u64(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 2^64."""
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    for a in (2, 3, 5, 7, 11, 13, 17):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def verify_pocklington_prime(
    n: int, factors: tuple[int, ...], witnesses: dict[int, int]
) -> None:
    """Verify primality from a complete factorization of n - 1."""
    assert prod(factors) == n - 1, "factorization does not multiply to n - 1"
    for q in set(factors):
        assert q in witnesses, f"missing Pocklington witness for factor {q}"
        a = witnesses[q]
        assert pow(a, n - 1, n) == 1, f"Fermat witness failed for factor {q}"
        assert gcd(pow(a, (n - 1) // q, n) - 1, n) == 1, (
            f"Pocklington gcd witness failed for factor {q}"
        )


@dataclass(frozen=True)
class ContractResult:
    n: int
    p: int
    q: int
    generator: int
    q_factorization: tuple[int, ...]
    p_prime_pocklington: bool
    p_minus_1_factorization: tuple[int, ...]
    g_pow_n_eq_one: bool
    g_pow_half_eq_minus_one: bool
    exact_order_n: bool
    result_json_checked: bool
    independent_verify_json_checked: bool
    independent_verify_status: str | None
    phi_window_domain_size: int
    merged_count: int | None
    collision_count: int | None
    injective: bool | None
    phi_image_sha256: str | None
    sorted_record_stream_sha256: str | None


def verify_arithmetic() -> tuple[bool, bool, bool]:
    assert N == 2**30
    assert P - 1 == N * Q
    assert Q == prod(Q_FACTORS)
    assert LARGE_Q_FACTOR - 1 == prod(LARGE_Q_FACTOR_FACTORS)
    for factor in set(Q_FACTORS) | set(LARGE_Q_FACTOR_FACTORS):
        if factor != LARGE_Q_FACTOR:
            assert is_prime_u64(factor), factor

    verify_pocklington_prime(
        LARGE_Q_FACTOR,
        LARGE_Q_FACTOR_FACTORS,
        LARGE_Q_FACTOR_POCKLINGTON_WITNESSES,
    )
    verify_pocklington_prime(P, (2,) * 30 + Q_FACTORS, P_POCKLINGTON_WITNESSES)

    g_pow_n = pow(G, N, P) == 1
    g_pow_half = pow(G, N // 2, P) == P - 1
    exact_order = g_pow_n and g_pow_half
    assert exact_order
    return g_pow_n, g_pow_half, exact_order


def verify_result_json(
    path: Path | None,
) -> tuple[bool, int | None, int | None, bool | None, str | None, str | None]:
    if path is None:
        return False, None, None, None, None, None

    data = json.loads(path.read_text())
    assert int(data["n"]) == N
    assert int(data["p"]) == P
    assert int(data["q"]) == Q
    assert int(data["generator"]) == G
    assert int(data["domain_size"]) == DOMAIN_SIZE
    assert int(data["merged_count"]) == DOMAIN_SIZE
    assert int(data["collision_count"]) == 0
    assert data["injective"] is True
    assert data["phi_image_sha256"] == PHI_IMAGE_SHA256
    assert data["sorted_record_stream_sha256"] == SORTED_RECORD_STREAM_SHA256

    return (
        True,
        int(data["merged_count"]),
        int(data["collision_count"]),
        bool(data["injective"]),
        str(data["phi_image_sha256"]),
        str(data["sorted_record_stream_sha256"]),
    )


def verify_independent_json(path: Path | None) -> tuple[bool, str | None]:
    if path is None:
        return False, None

    data = json.loads(path.read_text())
    assert data["status"] == "verified"
    assert data["mismatches"] == {}
    assert int(data["n"]) == N
    assert int(data["p"]) == P
    assert int(data["q"]) == Q
    assert int(data["generator"]) == G
    assert int(data["domain_size"]) == DOMAIN_SIZE
    assert int(data["chunk_records_sum"]) == DOMAIN_SIZE

    recomputed = data["recomputed"]
    expected = data["expected"]
    assert recomputed == expected
    assert int(recomputed["merged_count"]) == DOMAIN_SIZE
    assert int(recomputed["collision_count"]) == 0
    assert recomputed["first_collision"] is None
    assert recomputed["injective"] is True
    assert recomputed["phi_image_sha256"] == PHI_IMAGE_SHA256
    assert recomputed["sorted_record_stream_sha256"] == SORTED_RECORD_STREAM_SHA256
    return True, str(data["status"])


def run(result_json: Path | None, verify_json: Path | None) -> ContractResult:
    g_pow_n, g_pow_half, exact_order = verify_arithmetic()
    (
        result_checked,
        merged_count,
        collision_count,
        injective,
        phi_hash,
        stream_hash,
    ) = verify_result_json(result_json)
    independent_checked, independent_status = verify_independent_json(verify_json)
    return ContractResult(
        n=N,
        p=P,
        q=Q,
        generator=G,
        q_factorization=Q_FACTORS,
        p_prime_pocklington=True,
        p_minus_1_factorization=(2,) * 30 + Q_FACTORS,
        g_pow_n_eq_one=g_pow_n,
        g_pow_half_eq_minus_one=g_pow_half,
        exact_order_n=exact_order,
        result_json_checked=result_checked,
        independent_verify_json_checked=independent_checked,
        independent_verify_status=independent_status,
        phi_window_domain_size=DOMAIN_SIZE,
        merged_count=merged_count,
        collision_count=collision_count,
        injective=injective,
        phi_image_sha256=phi_hash,
        sorted_record_stream_sha256=stream_hash,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--result-json",
        type=Path,
        help="Optional release result JSON to check against the arithmetic row.",
    )
    parser.add_argument(
        "--verify-json",
        type=Path,
        help="Optional independent verifier JSON to check against the arithmetic row.",
    )
    args = parser.parse_args()
    print(json.dumps(asdict(run(args.result_json, args.verify_json)), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
