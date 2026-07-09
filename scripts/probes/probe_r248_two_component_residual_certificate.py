#!/usr/bin/env python3
"""#466 R248: two-component trim-five residual certificate scan.

R247 refutes literal monotonicity of H(theta)=S(theta)exp(theta/2): isolated
high residual spikes cause bumps.  This probe asks whether the R245 residual
CDF theorem can be split into two simpler statements:

* a middle-bulk cap on S(tau), and
* a high-tail half-rate cap only above a cutoff kappa > tau.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def max_half_rate_above(residual: np.ndarray, m: int, cutoff: float) -> tuple[float, float, int]:
    best = (0.0, cutoff, 0)
    for idx, x0 in enumerate(residual, start=1):
        theta = float(x0)
        if theta < cutoff:
            break
        h = (idx / m) * math.exp(theta / 2.0)
        if h > best[0]:
            best = (h, theta, idx)
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
    parser.add_argument("--tau", type=float, default=0.75)
    parser.add_argument(
        "--cutoffs",
        type=float,
        nargs="+",
        default=[0.875, 1.0, 1.125, 1.25, 1.5, 1.75, 2.0],
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

    print(f"R248 two-component residual certificate cases={len(cases)} trim={args.trim} tau={args.tau}")
    print("cutoff  bulk_S(tau) bulk_arg(n,p,M)      high_C   high_theta count high_arg(n,p,M)")
    print("-" * 112)
    for cutoff in args.cutoffs:
        bulk_rows = []
        high_rows = []
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            bulk_s = int(np.count_nonzero(residual >= args.tau)) / case.m
            bulk_rows.append((bulk_s, case.n, case.p, case.m))
            high_c, theta, count = max_half_rate_above(residual, case.m, cutoff)
            high_rows.append((high_c, theta, count, case.n, case.p, case.m))
        bulk_rows.sort(reverse=True)
        high_rows.sort(reverse=True)
        b = bulk_rows[0]
        h = high_rows[0]
        print(
            f"{cutoff:<7.3f} {b[0]:<11.6f} {b[1]},{b[2]},{b[3]:<13d} "
            f"{h[0]:<8.6f} {h[1]:<10.6f} {h[2]:<5d} {h[3]},{h[4]},{h[5]}"
        )

    print("\ninterpretation")
    print(
        "For theta in [tau, cutoff), the bulk cap alone implies "
        "S(theta) exp(theta/2) <= bulk_S(tau) exp(cutoff/2)."
    )


if __name__ == "__main__":
    main()
