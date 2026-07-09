#!/usr/bin/env python3
"""#466 R237: scaling laws for the top-five exponential contribution.

R233 reduced the top-five part of the live certificate to a cap on

    sum_{i<=5} exp(X_i / 4) / M.

This probe tests simple normalizations of the numerator over cached exact
spectra, looking for a theorem-shaped target such as `O(sqrt(M))` or
`O(sqrt(M log M))`.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=8)
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    rows = []
    for case in cases:
        top = case.desc[: min(args.trim, len(case.desc))]
        mass = float(np.exp(top / 4).sum())
        m = case.m
        lm = math.log(m)
        rows.append(
            (
                mass / m,
                mass / math.sqrt(m),
                mass / math.sqrt(m * lm),
                mass / (lm * lm),
                mass,
                float(case.desc[0]),
                float(case.desc[min(args.trim - 1, len(case.desc) - 1)]),
                m,
                case.n,
                case.p,
                case.label,
            )
        )

    print(f"R237 top-five scaling laws cases={len(rows)} trim={args.trim}")
    metrics = [
        ("mass/M", 0),
        ("mass/sqrtM", 1),
        ("mass/sqrtMlogM", 2),
        ("mass/logM^2", 3),
        ("mass", 4),
    ]
    for name, idx in metrics:
        ordered = sorted(rows, key=lambda row: row[idx], reverse=True)
        print(f"\nworst {name}")
        print("value      mass      mass/M    maxX     fifth    M      n     p          label")
        print("-" * 104)
        for row in ordered[: args.top]:
            print(
                f"{row[idx]:<10.6f} {row[4]:<9.3f} {row[0]:<9.6f} "
                f"{row[5]:<8.3f} {row[6]:<8.3f} {row[7]:<6d} {row[8]:<5d} {row[9]:<10d} {row[10]}"
            )

    print("\nsummary")
    if rows:
        for name, idx in metrics:
            worst = max(rows, key=lambda row: row[idx])
            print(
                f"max_{name.replace('/', '_per_')}={worst[idx]:.8f} "
                f"n={worst[8]} p={worst[9]} M={worst[7]} mass={worst[4]:.6f}"
            )


if __name__ == "__main__":
    main()
