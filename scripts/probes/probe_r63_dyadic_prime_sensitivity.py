#!/usr/bin/env python3
"""#466 R63: dyadic prime-sensitivity for normalized moments.

R62 showed that non-dyadic subgroup orders can have prime-sensitive arithmetic
spikes in their Gauss-period spectra.  This probe asks whether the prize
dyadic family μ_{2^a} has the same pathology or whether its normalized moment
ratios stay monotone across many admissible primes.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (
    coset_mags2,
    first_prime_congruent_one,
    ratios_from_cosets,
    subgroup,
)


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    from scripts.probes.probe_r59_large_moment_ratio_monotonicity import is_prime

    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def first_failure(rs: list[float]) -> tuple[int, float, float] | None:
    for i in range(len(rs) - 1):
        if rs[i + 1] > rs[i] + 1e-9:
            return i + 1, rs[i], rs[i + 1]
    return None


def summarize(n: int, starts: list[tuple[str, int, int]], max_r: int) -> None:
    print(f"n={n} max_r={max_r}")
    for label, start, count in starts:
        failures = []
        min_gap = float("inf")
        worst_tail = None
        for p in next_primes_congruent_one(n, start, count):
            mags = coset_mags2(p, subgroup(p, n))
            rs = ratios_from_cosets(p, n, mags, max_r)
            fail = first_failure(rs)
            if fail:
                failures.append((p, fail, max(rs)))
            gaps = [rs[i] - rs[i + 1] for i in range(len(rs) - 1)]
            gap = min(gaps)
            if gap < min_gap:
                min_gap = gap
                worst_tail = (p, rs)
        print(
            f"  {label:8s} start={start:<10d} primes={count:<2d} "
            f"failures={len(failures)} min_gap={min_gap:.6g}"
        )
        if failures:
            for p, fail, max_rval in failures[:5]:
                print(
                    f"    FAIL p={p} R{fail[0]}={fail[1]:.6g}"
                    f"<R{fail[0]+1}={fail[2]:.6g} maxR={max_rval:.6g}"
                )
        elif worst_tail is not None:
            p, rs = worst_tail
            head = " ".join(f"R{i+1}={x:.5f}" for i, x in enumerate(rs[:6]))
            tail = " ".join(
                f"R{max_r-3+i}={rs[max_r-4+i]:.5g}" for i in range(4)
            )
            print(f"    closest p={p} {head} ... {tail}")


def main() -> None:
    summarize(32, [("n^3", 32**3, 8), ("n^4", 32**4, 8)], 16)
    summarize(64, [("n^3", 64**3, 8), ("n^4", 64**4, 5)], 16)
    # n=128 at n^4 is already ~2e6 cosets per prime; test fewer primes.
    summarize(128, [("n^3", 128**3, 5), ("n^4", 128**4, 2)], 12)

    anchor_p = first_prime_congruent_one(256, 256**3)
    print(f"n=256 anchor p={anchor_p}")
    mags = coset_mags2(anchor_p, subgroup(anchor_p, 256))
    rs = ratios_from_cosets(anchor_p, 256, mags, 8)
    print(
        f"  failures={first_failure(rs)} "
        + " ".join(f"R{i+1}={x:.5f}" for i, x in enumerate(rs))
    )


if __name__ == "__main__":
    main()
