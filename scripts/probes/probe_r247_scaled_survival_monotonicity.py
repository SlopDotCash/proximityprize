#!/usr/bin/env python3
"""#466 R247: exact jump monotonicity of the trim-five scaled survival.

R246 suggests the half-rate scaled survival

    H(theta) = S(theta) * exp(theta/2)

is decreasing on the useful band theta >= 0.75.  This probe checks that at
every exact residual order-statistic jump in the cached spectra.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def jump_rows(residual: np.ndarray, m: int, tau: float) -> list[tuple[float, float, int]]:
    rows = []
    for idx, theta0 in enumerate(residual, start=1):
        theta = float(theta0)
        if theta < tau:
            break
        rows.append((theta, (idx / m) * math.exp(theta / 2.0), idx))
    return rows


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
    parser.add_argument("--tau", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=20)
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

    worst_rows = []
    violation_rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        rows = jump_rows(residual, case.m, args.tau)
        if not rows:
            continue
        best = max((h, theta, count) for theta, h, count in rows)
        first = rows[-1]  # closest jump to tau from above, since residual descends.
        worst_rows.append((best[0], best[1], best[2], first[0], first[1], first[2], case.n, case.p, case.m))

        # In descending theta order, H should increase as theta descends toward tau.
        max_so_far = -1.0
        for theta, h, count in rows:
            if h + 1.0e-12 < max_so_far:
                violation_rows.append((max_so_far - h, theta, h, count, case.n, case.p, case.m))
            max_so_far = max(max_so_far, h)

    worst_rows.sort(reverse=True)
    violation_rows.sort(reverse=True)

    print(f"R247 exact scaled survival monotonicity cases={len(cases)} trim={args.trim} tau={args.tau}")
    print("\nworst exact H(theta)=S(theta)exp(theta/2)")
    print("Hmax     theta*    count* tauEdge  Hedge    edgeCnt n     p          M")
    print("-" * 100)
    for row in worst_rows[: args.top]:
        h, theta, count, edge_theta, edge_h, edge_count, n, p, m = row
        print(
            f"{h:<8.6f} {theta:<9.6f} {count:<6d} {edge_theta:<8.6f} "
            f"{edge_h:<8.6f} {edge_count:<7d} {n:<5d} {p:<10d} {m}"
        )

    print("\nmonotonicity violations")
    print(f"violations={len(violation_rows)}")
    if violation_rows:
        print("drop     theta     H        count  n     p          M")
        print("-" * 72)
        for drop, theta, h, count, n, p, m in violation_rows[: args.top]:
            print(f"{drop:<8.6f} {theta:<9.6f} {h:<8.6f} {count:<6d} {n:<5d} {p:<10d} {m}")


if __name__ == "__main__":
    main()
