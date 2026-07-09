#!/usr/bin/env python3
"""#466 R259: coupled tradeoffs between high survival and thin-band mass.

R258 refutes independent caps on S(hi) and band([0.75,hi)).  This probe scans
linear coupled envelopes

    S(hi) + lambda * band <= K(lambda)

and reports whether they can imply a sharp cap on S(0.75) = S(hi)+band.
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
    parser.add_argument("--lo", type=float, default=0.75)
    parser.add_argument("--hi", type=float, default=0.79049)
    parser.add_argument("--target-slo", type=float, default=0.4121212122)
    parser.add_argument("--top", type=int, default=12)
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

    points = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        s_lo = int(np.count_nonzero(residual >= args.lo)) / case.m
        s_hi = int(np.count_nonzero(residual >= args.hi)) / case.m
        band = s_lo - s_hi
        points.append((s_hi, band, s_lo, case.n, case.p, case.m))

    lambdas = [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0, 4.0]
    print(f"R259 coupled band tradeoff cases={len(points)} lo={args.lo} hi={args.hi}")
    print("lambda  K        argK(n,p,M)          maxSloUnderK?  worstSlo  argSlo(n,p,M)")
    print("-" * 108)
    for lam in lambdas:
        best = max(points, key=lambda r: (r[0] + lam * r[1], r[3], r[4], r[5]))
        K = best[0] + lam * best[1]
        # If lambda >= 1, then Slo = Shi+band <= K.  If lambda < 1, this
        # coupled inequality alone cannot upper-bound Slo without another band cap.
        implied = K if lam >= 1.0 else float("nan")
        worst_slo = max(points, key=lambda r: (r[2], r[3], r[4], r[5]))
        print(
            f"{lam:<7.2f} {K:<8.6f} {best[3]},{best[4]},{best[5]:<14d} "
            f"{implied:<14.6f} {worst_slo[2]:<8.6f} "
            f"{worst_slo[3]},{worst_slo[4]},{worst_slo[5]}"
        )

    print("\nupper hull candidates by Slo")
    rows = sorted(points, key=lambda r: (r[2], r[0]), reverse=True)[: args.top]
    print("Slo      Shi      band     n     p          M")
    print("-" * 72)
    for s_hi, band, s_lo, n, p, m in rows:
        print(f"{s_lo:<8.6f} {s_hi:<8.6f} {band:<8.6f} {n:<5d} {p:<10d} {m}")


if __name__ == "__main__":
    main()
