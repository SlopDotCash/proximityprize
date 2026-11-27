#!/usr/bin/env python3
"""Exact integer norm certifier & cyclotomic-unit sieve for QuarterDyadicEigenspaceExclusion.lean.

1. Uses 100% pure-integer outward-rounded interval arithmetic (zero floating point) to certify:
   - Uniform |N_{Q(zeta_32)/Q}(1 - rho)| < 2^120 for ALL disjoint A, B in mu_32 with |A|, |B| <= 7;
   - Uniform |N_{Q(zeta_32)/Q}(1 - rho)| < 2^150 for ALL disjoint A, B in mu_32 with |A|, |B| <= 15.
2. Compiles and runs probe_quarter_dyadic_eigenspace_sieve.cpp at BOTH m = 101 and m = 103
   across all 6,903 rotation+Galois orbits of 7-subsets of mu_32 (summing to C(32, 7) = 3,365,856),
   certifying ZERO ternary kernel vectors for the sole constant-phase s = 1 pair (7, 6).
"""
from __future__ import annotations

from functools import cache
from math import isqrt, prod
from pathlib import Path
import subprocess
import tempfile
import numpy as np

N = 32
SCALE = 1 << 100
PRIME_1 = (1 << 158) + 192 * (1 << 30) + 1
PRIME_2 = (1 << 159) + 13 * (1 << 30) + 1


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


@cache
def twice_cos(n: int, t: int) -> tuple[int, int]:
    t %= n
    if n == 2:
        v = (-1 if t else 1) * 2 * SCALE
        return v, v
    if 4 * t in (n, 3 * n):
        return 0, 0
    lo, hi = twice_cos(n // 2, t % (n // 2))
    lo = isqrt(max(0, (2 * SCALE + lo) * SCALE))
    hi = isqrt((2 * SCALE + hi) * SCALE) + 1
    return (-hi, -lo) if n < 4 * t < 3 * n else (lo, hi)


@cache
def chord(t: int) -> tuple[int, int]:
    lo, hi = twice_cos(N, t % N)
    return isqrt(max(0, (2 * SCALE - hi) * SCALE)), isqrt((2 * SCALE - lo) * SCALE) + 1


def uniform_norm_bound(shift: int, dmax: int) -> int:
    """Exact integer upper bound on |N_{Q(zeta_32)/Q}(1 - rho)| for ALL 0 <= |A|, |B| <= dmax."""
    sites = [a for a in range(1, N) if a != shift]
    rows = []
    for u in range(1, N // 2, 2):
        bnds = []
        for a in sites:
            left = chord((u * a) % N)
            right = chord((u * (a - shift)) % N)
            assert min(*left, *right) > 0
            bnds.append((SCALE * left[0] // right[1], ceil_div(SCALE * left[1], right[0])))
        rows.append(bnds)

    total = 0

    def visit(i: int, lo: list[int], hi: list[int], mult: int) -> None:
        nonlocal total
        if i == len(rows):
            pos_hi = sorted((v for v in hi if v > SCALE), reverse=True)[:dmax]
            neg_lo = sorted(v for v in lo if v < SCALE)[:dmax]
            num = prod(pos_hi) * (SCALE ** len(neg_lo))
            den = prod(neg_lo) * (SCALE ** len(pos_hi))
            total += mult * ceil_div(num, den)
            return
        visit(i + 1, lo, hi, mult)
        for exp in (1, 2):
            lo = [a * b[0] // SCALE for a, b in zip(lo, rows[i])]
            hi = [ceil_div(a * b[1], SCALE) for a, b in zip(hi, rows[i])]
            visit(i + 1, lo, hi, mult * (2 if exp == 1 else 1))

    visit(0, [SCALE] * len(sites), [SCALE] * len(sites), 1)
    return total


def verify_regulator_8() -> None:
    reg = np.array([
        [np.log(2.0 * np.sin(np.pi * (((2 * e + 1) * (2 * k + 1)) % N) / N)) for k in range(8)]
        for e in range(8)
    ])
    det = float(np.linalg.det(reg))
    assert abs(det) > 10.0
    print(f"Verified 8x8 mu_32 cyclotomic log regulator det = {det:.6f}", flush=True)


def main() -> None:
    for dmax, bit_cap in [(7, 120), (15, 150)]:
        worst = max(uniform_norm_bound(sh, dmax) for sh in (1, 2, 4, 8, 16))
        assert worst < (1 << bit_cap) < PRIME_1 < PRIME_2
        print(
            f"Uniform Q(zeta_32) norm for ALL 0 <= |A|,|B| <= {dmax}: "
            f"bit_length={worst.bit_length()} < 2^{bit_cap} < p1 < p2",
            flush=True,
        )
    verify_regulator_8()
    src = Path(__file__).with_name("probe_quarter_dyadic_eigenspace_sieve.cpp")
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "dyadic_eigenspace_sieve"
        subprocess.run(["c++", "-O3", "-std=c++17", str(src), "-o", str(exe)], check=True)
        subprocess.run([str(exe)], check=True)


if __name__ == "__main__":
    main()
