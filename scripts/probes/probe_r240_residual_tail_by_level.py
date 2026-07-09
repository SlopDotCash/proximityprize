#!/usr/bin/env python3
"""#466 R240: residual tail profile by dyadic level.

R238/R239 identify the first residual band after top-five deletion as the live
tail obstruction.  This probe groups the scaled residual tail constants by
dyadic level `n`, to see whether the worst case is a finite-level phenomenon or
stable across the tower.
"""

from __future__ import annotations

import argparse
import math
import sys
from collections import defaultdict
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
    parser.add_argument(
        "--thetas",
        type=float,
        nargs="+",
        default=[0.75, 0.8, 0.875, 1.0, 1.25, 1.5, 2.0],
    )
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
    by_n: dict[int, list] = defaultdict(list)
    for case in cases:
        by_n[case.n].append(case)

    print(
        f"R240 residual tail by level cases={len(cases)} "
        f"trim={args.trim} n_levels={sorted(by_n)}"
    )
    for theta in args.thetas:
        print(f"\ntheta={theta}")
        print("scope   cases  scaled    frac      count  M      n     p          label")
        print("-" * 100)
        scopes: list[tuple[str, list]] = [("all", cases)] + [
            (f"n={n}", level_cases) for n, level_cases in sorted(by_n.items())
        ]
        for scope, scope_cases in scopes:
            best = None
            for case in scope_cases:
                residual = case.desc[min(args.trim, len(case.desc)) :]
                count = int(np.count_nonzero(residual >= theta))
                frac = count / case.m
                scaled = frac * math.exp(theta / 2.0)
                row = (scaled, frac, count, case.m, case.n, case.p, case.label)
                if best is None or row > best:
                    best = row
            if best is None:
                continue
            scaled, frac, count, m, n, p, label = best
            print(
                f"{scope:<7s} {len(scope_cases):<6d} {scaled:<9.6f} {frac:<9.6f} "
                f"{count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
            )


if __name__ == "__main__":
    main()
