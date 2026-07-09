#!/usr/bin/env python3
"""#466 R202: test a medium-index direct / large-spike split.

R196 showed that very small coset counts should be handled by direct
quarter-MGF certificates.  R200 then found the largest large-branch spike
ratio near the lower edge, around M=36.  This probe tests the stronger split:

    M < M0       -> direct MGF(1/4) <= 2 certificate,
    M >= M0      -> spike-ratio / log-max route.

It exhausts dyadic rows p = M*n + 1 prime for M < M0 through a configurable
2-adic depth, and separately reports large-anchor spike-ratio diagnostics for
M >= M0 using the R200 vectorized case set.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import is_prime  # noqa: E402
from scripts.probes.probe_r199_vectorized_large_anchor_tail import normalized_values_vectorized  # noqa: E402
from scripts.probes.probe_r200_vectorized_large_grid_sweep import case_set  # noqa: E402


def medium_rows(
    max_a: int, split_index: int, chunk: int
) -> list[tuple[float, float, float, int, int, int, int]]:
    rows = []
    for a in range(3, max_a + 1):
        n = 2**a
        for m_index in range(2, split_index):
            p = m_index * n + 1
            if is_prime(p):
                xs = normalized_values_vectorized(p, n, chunk)
                max_x = float(xs.max())
                rows.append(
                    (
                        float((math.e ** (xs / 4)).mean()),
                        math.exp(max_x / 4) / len(xs),
                        max_x,
                        len(xs),
                        n,
                        p,
                        a,
                    )
                )
    return rows


def large_rows(
    split_index: int, max_n: int, max_p: int, primes_per_start: int, chunk: int
) -> list[tuple[float, float, float, int, int, int, str]]:
    rows = []
    for n, p, label in sorted(case_set(max_n, max_p, primes_per_start)):
        m = (p - 1) // n
        if m < split_index:
            continue
        xs = normalized_values_vectorized(p, n, chunk)
        max_x = float(xs.max())
        rows.append(
            (
                float((math.e ** (xs / 4)).mean()),
                math.exp(max_x / 4) / len(xs),
                max_x,
                len(xs),
                n,
                p,
                label,
            )
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--split-index", type=int, default=1024)
    parser.add_argument("--medium-max-a", type=int, default=14)
    parser.add_argument("--large-max-n", type=int, default=512)
    parser.add_argument("--large-max-p", type=int, default=350_000_000)
    parser.add_argument("--large-primes-per-start", type=int, default=1)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--spike-target", type=float, default=0.19978553854516545)
    args = parser.parse_args()

    medium = medium_rows(args.medium_max_a, args.split_index, args.chunk)
    large = large_rows(
        args.split_index,
        args.large_max_n,
        args.large_max_p,
        args.large_primes_per_start,
        args.chunk,
    )

    medium_by_mgf = sorted(medium, reverse=True)
    medium_by_ratio = sorted(medium, key=lambda r: r[1], reverse=True)
    large_by_ratio = sorted(large, key=lambda r: r[1], reverse=True)
    large_by_mgf = sorted(large, reverse=True)

    medium_viol = [row for row in medium if row[0] > 2 + 1e-12]
    large_viol = [row for row in large if row[1] > args.spike_target + 1e-12]

    print(
        f"R202 medium-direct / large-spike split: split_index={args.split_index} "
        f"medium_tested={len(medium)} large_tested={len(large)}"
    )
    print(
        f"medium_mgf_violations={len(medium_viol)} "
        f"large_spike_target_violations={len(large_viol)} target={args.spike_target:.6f}"
    )

    print("\nworst medium direct MGF rows")
    print("mgf1/4  spike/M   maxX    M     n       p          a")
    print("-" * 72)
    for mgf4, ratio, max_x, m, n, p, a in medium_by_mgf[:25]:
        print(f"{mgf4:<7.4f} {ratio:<9.6f} {max_x:<7.3f} {m:<5d} {n:<7d} {p:<10d} {a}")

    print("\nworst medium spike-ratio rows")
    print("spike/M   mgf1/4  maxX    M     n       p          a")
    print("-" * 72)
    for mgf4, ratio, max_x, m, n, p, a in medium_by_ratio[:25]:
        print(f"{ratio:<9.6f} {mgf4:<7.4f} {max_x:<7.3f} {m:<5d} {n:<7d} {p:<10d} {a}")

    print("\nworst large spike-ratio rows")
    print("spike/M   mgf1/4  maxX    M        n     p          label")
    print("-" * 92)
    for mgf4, ratio, max_x, m, n, p, label in large_by_ratio[:25]:
        print(f"{ratio:<9.6f} {mgf4:<7.4f} {max_x:<7.3f} {m:<8d} {n:<5d} {p:<10d} {label}")

    print("\nsummary")
    if medium_by_mgf:
        worst = medium_by_mgf[0]
        print(
            "worst_medium_mgf="
            f"{worst[0]:.6f} spike_ratio={worst[1]:.6f} "
            f"M={worst[3]} n={worst[4]} p={worst[5]}"
        )
    if large_by_ratio:
        worst = large_by_ratio[0]
        print(
            "worst_large_spike_ratio="
            f"{worst[1]:.6f} mgf={worst[0]:.6f} "
            f"M={worst[3]} n={worst[4]} p={worst[5]} label={worst[6]}"
        )
    if large_by_mgf:
        worst = large_by_mgf[0]
        print(
            "worst_large_mgf="
            f"{worst[0]:.6f} spike_ratio={worst[1]:.6f} "
            f"M={worst[3]} n={worst[4]} p={worst[5]} label={worst[6]}"
        )


if __name__ == "__main__":
    main()
