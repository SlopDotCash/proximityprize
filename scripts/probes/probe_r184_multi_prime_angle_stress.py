#!/usr/bin/env python3
"""#466 R184: multi-prime stress for child-pair angle equidistribution."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r183_child_pair_angle_equidistribution import angle_stats  # noqa: E402
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import is_prime  # noqa: E402


def primes_congruent_one(modulus: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % modulus)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += modulus
    return out


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    max_n = int(sys.argv[2]) if len(sys.argv) > 2 else 32
    for n in (16, 32, 64):
        if n > max_n:
            break
        print(f"n {n} -> {2*n}")
        ps = primes_congruent_one(2 * n, max((2 * n) ** 4, 100_000), count)
        for p in ps:
            st = angle_stats(p, n)
            print(
                f"{p} pairs {int(st['m'])} disc16 {st['disc']:.5f} "
                f"maxF {st['max_f1_8']:.5f} f4 {st['f4']:.5f}"
            )


if __name__ == "__main__":
    main()
