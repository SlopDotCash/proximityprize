#!/usr/bin/env python3
"""#466 R238: residual tail after deleting top five quotient orbits.

R231/R237 split the live MGF route into:

* top-five contribution;
* residual survival tail after deleting the top five.

This probe isolates the second part.  For each exact quotient spectrum it
computes the required `C` in

    #{residual X >= theta} <= C * M * exp(-theta/2),  theta > tau,

after deleting the top `trim` values.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def residual_required_c(desc, trim: int, tau: float) -> tuple[float, float, int]:
    m = len(desc)
    best = (0.0, tau, 0)
    for idx, x0 in enumerate(desc[min(trim, m) :], start=1):
        theta = float(x0)
        if theta <= tau:
            break
        c_req = (idx / m) * math.exp(theta / 2.0)
        if c_req > best[0]:
            best = (c_req, theta, idx)
    return best


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
    parser.add_argument("--taus", type=float, nargs="+", default=[0.5, 0.625, 0.75, 0.875, 1.0])
    parser.add_argument("--target-c", type=float, default=0.6012)
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

    all_rows = []
    print(f"R238 trim-{args.trim} residual tail cases={len(cases)} target_C={args.target_c}")
    for tau in args.taus:
        rows = []
        for case in cases:
            c_req, theta, count = residual_required_c(case.desc, args.trim, tau)
            rows.append((c_req, theta, count, case.m, case.n, case.p, case.label))
        rows.sort(reverse=True)
        all_rows.append((tau, rows[0] if rows else None))
        print(f"\ntau={tau}")
        print("C_req    slack    theta     count  M      n     p          label")
        print("-" * 92)
        for c_req, theta, count, m, n, p, label in rows[: args.top]:
            print(
                f"{c_req:<8.6f} {args.target_c-c_req:<8.6f} {theta:<9.6f} "
                f"{count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
            )
        if rows:
            print(
                f"summary tau={tau}: worst_C={rows[0][0]:.8f} "
                f"slack={args.target_c-rows[0][0]:.8f} n={rows[0][4]} p={rows[0][5]} M={rows[0][3]}"
            )

    print("\noverall")
    for tau, row in all_rows:
        if row is None:
            continue
        print(f"tau={tau} worst_C={row[0]:.8f} slack={args.target_c-row[0]:.8f} n={row[4]} p={row[5]} M={row[3]}")


if __name__ == "__main__":
    main()
