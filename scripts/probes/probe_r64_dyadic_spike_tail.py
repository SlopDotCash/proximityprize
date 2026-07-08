#!/usr/bin/env python3
"""#466 R64: dyadic spike height and tail-shape probe.

R63 refuted universal monotonicity for μ_{2^a}.  This probe measures whether
the failures are still controlled: peak height, peak location, and decay after
the peak across known adversarial dyadic primes and nearby admissible primes.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    is_prime,
    ratios_from_cosets,
    subgroup,
)


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def v2(m: int) -> int:
    out = 0
    while m % 2 == 0:
        out += 1
        m //= 2
    return out


def first_failure(rs: list[float]) -> tuple[int, float, float] | None:
    for i in range(len(rs) - 1):
        if rs[i + 1] > rs[i] + 1e-9:
            return i + 1, rs[i], rs[i + 1]
    return None


def profile(n: int, p: int, max_r: int) -> tuple[list[float], tuple[int, float], int | None]:
    rs = ratios_from_cosets(p, n, coset_mags2(p, subgroup(p, n)), max_r)
    peak = max(enumerate(rs, start=1), key=lambda x: x[1])
    after_peak = None
    for i in range(peak[0], len(rs)):
        if rs[i] <= 1.0 + 1e-9:
            after_peak = i + 1
            break
    return rs, peak, after_peak


def row(n: int, p: int, max_r: int) -> tuple[int, int, int, int, tuple[int, float, float] | None, tuple[int, float], int | None]:
    rs, peak, after_peak = profile(n, p, max_r)
    return n, p, (p - 1) // n, v2(p - 1), first_failure(rs), peak, after_peak


def main() -> None:
    cases: list[tuple[int, int, int]] = [
        (32, 32993, 24),
        (64, 264769, 24),
        (64, 265921, 24),
        (64, 16778497, 28),
        (128, 2101249, 20),
        (128, 268438657, 16),
        (256, 16777729, 14),
    ]
    for n in (32, 64, 128):
        cases.extend((n, p, 20 if n <= 64 else 16) for p in next_primes_congruent_one(n, n**4, 4))

    seen = set()
    print("n   p          q        v2  fail                 peak        recover")
    print("-" * 82)
    for n, p, max_r in cases:
        if (n, p) in seen:
            continue
        seen.add((n, p))
        _, _, q, vp, fail, peak, after_peak = row(n, p, max_r)
        fail_s = "-" if fail is None else f"R{fail[0]}<{fail[0]+1} ({fail[2]-fail[1]:.3g})"
        recover_s = "-" if after_peak is None else f"R{after_peak}"
        print(
            f"{n:<3d} {p:<10d} {q:<8d} {vp:<3d} "
            f"{fail_s:<20s} R{peak[0]}={peak[1]:<9.5g} {recover_s}"
        )

    print("\nselected spectra")
    for n, p, max_r in [(32, 32993, 16), (64, 16778497, 16), (128, 2101249, 14)]:
        rs, peak, _ = profile(n, p, max_r)
        print(f"n={n} p={p} peak=R{peak[0]}={peak[1]:.6g}")
        print("  " + " ".join(f"R{i+1}={x:.5g}" for i, x in enumerate(rs)))


if __name__ == "__main__":
    main()
