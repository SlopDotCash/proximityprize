#!/usr/bin/env python3
"""#466 R261: CDF envelope ordering by dyadic level.

R260 refutes simple arithmetic fingerprints.  R261 asks whether the residual
CDF envelopes are ordered by dyadic level, which would suggest a tower/induction
route: prove the worst finite level and show higher levels improve.
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
        default=[0.5, 0.625, 0.75, 0.755, 0.8, 0.875, 1.0, 1.25, 1.5, 2.0],
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
    by_n = defaultdict(list)
    for case in cases:
        by_n[case.n].append(case)

    print(f"R261 level CDF envelope order cases={len(cases)} trim={args.trim}")
    print("theta   all      " + " ".join(f"n={n}" for n in sorted(by_n)))
    print("-" * 92)
    for theta in args.thetas:
        vals = []
        all_best = 0.0
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            s = int(np.count_nonzero(residual >= theta)) / case.m
            all_best = max(all_best, s)
        for n in sorted(by_n):
            best = 0.0
            for case in by_n[n]:
                residual = case.desc[min(args.trim, len(case.desc)) :]
                s = int(np.count_nonzero(residual >= theta)) / case.m
                best = max(best, s)
            vals.append(best)
        print(f"{theta:<7.3f} {all_best:<8.6f} " + " ".join(f"{v:<8.6f}" for v in vals))

    print("\nscaled half-rate envelope by level")
    print("theta   all      " + " ".join(f"n={n}" for n in sorted(by_n)))
    print("-" * 92)
    for theta in args.thetas:
        vals = []
        all_best = 0.0
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            h = (int(np.count_nonzero(residual >= theta)) / case.m) * math.exp(theta / 2.0)
            all_best = max(all_best, h)
        for n in sorted(by_n):
            best = 0.0
            for case in by_n[n]:
                residual = case.desc[min(args.trim, len(case.desc)) :]
                h = (int(np.count_nonzero(residual >= theta)) / case.m) * math.exp(theta / 2.0)
                best = max(best, h)
            vals.append(best)
        print(f"{theta:<7.3f} {all_best:<8.6f} " + " ".join(f"{v:<8.6f}" for v in vals))

    print("\nlevel winners")
    for theta in args.thetas:
        winners = []
        for n in sorted(by_n):
            best = max(
                (int(np.count_nonzero(case.desc[min(args.trim, len(case.desc)) :] >= theta)) / case.m, case)
                for case in by_n[n]
            )
            winners.append((best[0], n, best[1].p, best[1].m))
        winner = max(winners)
        print(f"theta={theta:<5.3f} winner n={winner[1]} p={winner[2]} M={winner[3]} S={winner[0]:.8f}")


if __name__ == "__main__":
    main()
