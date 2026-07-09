#!/usr/bin/env python3
"""#466 R258: rounded constant packages for the R257 split.

R257 splits the R251 micro-band cap into

    S(0.75) <= S(hi) + mass([0.75, hi)).

This probe searches for theorem-grade decimal/rational-ish constants

    S(hi) <= A,  band <= B

with `(A+B) * exp(0.755/2) <= 0.6012`.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def ceil_step(x: float, step: float) -> float:
    return math.ceil((x - 1.0e-15) / step) * step


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
    parser.add_argument("--lo", type=float, default=0.75)
    parser.add_argument("--micro-cutoff", type=float, default=0.755)
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument("--round-step", type=float, default=0.0001)
    parser.add_argument(
        "--his",
        type=float,
        nargs="+",
        default=[0.77, 0.775, 0.78, 0.785, 0.79049, 0.795, 0.8, 0.81, 0.825],
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

    rows = []
    for hi in args.his:
        max_s_hi = (0.0, 0, 0, 0)
        max_band = (0.0, 0, 0, 0)
        max_sum = (0.0, 0, 0, 0)
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            s_lo = int(np.count_nonzero(residual >= args.lo)) / case.m
            s_hi = int(np.count_nonzero(residual >= hi)) / case.m
            band = s_lo - s_hi
            if (s_hi, case.n, case.p, case.m) > max_s_hi:
                max_s_hi = (s_hi, case.n, case.p, case.m)
            if (band, case.n, case.p, case.m) > max_band:
                max_band = (band, case.n, case.p, case.m)
            if (s_lo, case.n, case.p, case.m) > max_sum:
                max_sum = (s_lo, case.n, case.p, case.m)
        A = ceil_step(max_s_hi[0], args.round_step)
        B = ceil_step(max_band[0], args.round_step)
        package_cost = (A + B) * math.exp(args.micro_cutoff / 2.0)
        direct_cost = max_sum[0] * math.exp(args.micro_cutoff / 2.0)
        rows.append(
            (
                package_cost,
                direct_cost,
                A,
                B,
                max_s_hi,
                max_band,
                max_sum,
                hi,
            )
        )

    rows.sort()
    print(
        f"R258 constant package search cases={len(cases)} trim={args.trim} "
        f"target={args.target_c} step={args.round_step}"
    )
    print("hi       pkgCost  pkgSlack direct   A       B       maxShi(n,p,M)       maxBand(n,p,M)")
    print("-" * 116)
    for package_cost, direct_cost, A, B, max_s_hi, max_band, _max_sum, hi in rows:
        print(
            f"{hi:<8.5f} {package_cost:<8.6f} {args.target_c-package_cost:<8.6f} "
            f"{direct_cost:<8.6f} {A:<7.4f} {B:<7.4f} "
            f"{max_s_hi[0]:.6f},{max_s_hi[1]},{max_s_hi[2]},{max_s_hi[3]} "
            f"{max_band[0]:.6f},{max_band[1]},{max_band[2]},{max_band[3]}"
        )


if __name__ == "__main__":
    main()
