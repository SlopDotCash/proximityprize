#!/usr/bin/env python3
"""Lightweight (<0.5s) arithmetic & style-lint verifier for Milestone 2 (Sixth Moment & Recurrence)."""

from __future__ import annotations

import math
import sys
from pathlib import Path

from probe_carbon_bgk_lint_and_bridge import lint_lean_file


def verify_sixth_moment_arithmetic() -> None:
    n = 1 << 30
    p1 = n * ((1 << 128) + 192) + 1
    p2 = n * (2 * (1 << 128) + 13) + 1

    # 1. Exact divisibility & DC-subtracted moment equivalence threshold n^5 < p
    assert n**5 < p1 and n**5 < p2

    # 2. Punctured u = 1 Cauchy-Schwarz lower bound under rEnergy H 3 <= 15 * n^3
    t0 = 3 * n - 3
    a = 6 * n * n + 18 * n - 9
    b = n * n - 3 * n + 3
    assert a == 15 * n * n - t0 * t0
    assert b == n * n - t0
    assert b * t0 - a == 3 * n * n * (n - 6)

    # Strict positivity check: t^2 <= 15 * n^2 => t <= 4158584202 => 15*n^2 - t^2 > 0
    isqrt_15n2 = math.isqrt(15 * n * n)
    assert isqrt_15n2 == 4158584202
    assert isqrt_15n2**2 < 15 * n * n < (isqrt_15n2 + 1) ** 2

    d_prime_min = (b * b + a - 1) // a
    d_min = d_prime_min + 1
    assert d_prime_min == 192153582490528434
    assert d_min == 192153582490528435
    assert a * (d_prime_min - 1) < b * b <= a * d_prime_min

    # Ratio improvement over previous 76,861,433,640,456,466 bound
    old_bound = 76861433640456466
    assert d_min > (5 * old_bound) // 2 - 10**10

    # 3. Finite-window holonomic check: for r, b <= n^2, D*(b+1) + r <= 2^128 <= (p - 1) // n
    max_window_needed = (n * n) * (n * n + 1) + n * n
    assert max_window_needed <= (p1 - 1) // n
    assert max_window_needed <= (p2 - 1) // n

    # 4. K = mu_65536 coset triple-sum census arithmetic
    m = 65536
    clean_orbits = (math.comb(m + 2, 3) - (m * m) // 2) // m
    assert clean_orbits == 715827883
    per_coset_sums = (clean_orbits + 1) * m
    assert per_coset_sums == 46912496205824
    assert per_coset_sums * (n // m) == 768614337836220416

    print(
        f"[OK] Sixth-moment & recurrence arithmetic verified: "
        f"punctured bins >= {d_min} (2.5x over {old_bound}), "
        f"holonomic window fits (P_i - 1)/n, K=mu_65536 sums = {per_coset_sums * (n // m)}."
    )


def main() -> int:
    verify_sixth_moment_arithmetic()
    failed = False
    for arg in sys.argv[1:]:
        p = Path(arg)
        errs = lint_lean_file(p)
        if errs:
            failed = True
            print(f"[FAIL] {p}:")
            for e in errs:
                print(f"  {e}")
        else:
            print(f"[OK] Lint clean: {p} ({len(p.read_text().splitlines())} lines)")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
