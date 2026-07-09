#!/usr/bin/env python3
"""#466 R239: first residual band versus low moments.

R238 shows the residual tail is tight at the first live threshold tau=0.75.
This probe asks whether that first-band cap is explained by low moments of the
trimmed spectrum, or whether it is genuinely arithmetic/distributional.
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
    parser.add_argument("--theta", type=float, default=0.75)
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
        residual = case.desc[min(args.trim, len(case.desc)) :]
        count = int(np.count_nonzero(residual >= args.theta))
        frac = count / case.m
        scaled = frac * math.exp(args.theta / 2.0)
        mean = float(residual.mean())
        second = float((residual * residual).mean())
        mgf4 = float(np.exp(residual / 4.0).mean())
        rows.append((scaled, frac, count, mean, second, mgf4, float(residual[0]), case.m, case.n, case.p, case.label))

    rows.sort(reverse=True)
    print(
        f"R239 residual first-band moments cases={len(rows)} trim={args.trim} theta={args.theta}"
    )
    print("scaled   frac     count  mean     second   mgf1/4   maxRes   M      n     p          label")
    print("-" * 120)
    for row in rows[: args.top]:
        scaled, frac, count, mean, second, mgf4, max_res, m, n, p, label = row
        print(
            f"{scaled:<8.6f} {frac:<8.6f} {count:<6d} {mean:<8.5f} {second:<8.5f} "
            f"{mgf4:<8.5f} {max_res:<8.3f} {m:<6d} {n:<5d} {p:<10d} {label}"
        )

    print("\nsummary")
    if rows:
        worst = rows[0]
        print(
            f"worst_scaled={worst[0]:.8f} frac={worst[1]:.8f} "
            f"n={worst[8]} p={worst[9]} M={worst[7]}"
        )
        print(f"max_mean={max(r[3] for r in rows):.8f}")
        print(f"max_second={max(r[4] for r in rows):.8f}")
        print(f"max_residual_mgf1/4={max(r[5] for r in rows):.8f}")


if __name__ == "__main__":
    main()
