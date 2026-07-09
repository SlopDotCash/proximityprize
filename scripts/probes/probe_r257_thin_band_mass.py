#!/usr/bin/env python3
"""#466 R257: thin-band mass between 0.75 and the q60 cap.

R253/R256 identify `S(Q*) <= 0.40` with Q* ~= 0.79049 as a clean q60
statement.  But the R251 micro-band needs `S(0.75) <= 0.412121...`, so one
also needs to control the thin band [0.75, Q*).
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

    rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        s_lo = int(np.count_nonzero(residual >= args.lo)) / case.m
        s_hi = int(np.count_nonzero(residual >= args.hi)) / case.m
        band = s_lo - s_hi
        micro = s_lo * math.exp(0.755 / 2.0)
        rows.append((micro, band, s_lo, s_hi, case.n, case.p, case.m))

    rows.sort(reverse=True)
    by_band = sorted(rows, key=lambda r: r[1], reverse=True)
    print(f"R257 thin-band mass cases={len(rows)} trim={args.trim} band=[{args.lo},{args.hi})")
    print("\nworst micro rows")
    print("micro    band     Slo      Shi      n     p          M")
    print("-" * 76)
    for row in rows[: args.top]:
        micro, band, s_lo, s_hi, n, p, m = row
        print(f"{micro:<8.6f} {band:<8.6f} {s_lo:<8.6f} {s_hi:<8.6f} {n:<5d} {p:<10d} {m}")

    print("\nworst band rows")
    print("band     micro    Slo      Shi      n     p          M")
    print("-" * 76)
    for row in by_band[: args.top]:
        micro, band, s_lo, s_hi, n, p, m = row
        print(f"{band:<8.6f} {micro:<8.6f} {s_lo:<8.6f} {s_hi:<8.6f} {n:<5d} {p:<10d} {m}")

    vals = np.array([[r[0], r[1], r[2], r[3], r[6] / r[4], math.log(r[6])] for r in rows])
    names = ["micro", "band", "Slo", "Shi", "M/n", "logM"]
    print("\nsummary")
    for idx, name in enumerate(names):
        col = vals[:, idx]
        print(
            f"{name:<6s} median={float(np.median(col)):.6f} p95={float(np.quantile(col,0.95)):.6f} "
            f"max={float(np.max(col)):.6f}"
        )
    print("\ncorrelations")
    target = vals[:, 0]
    for idx, name in enumerate(names[1:], start=1):
        print(f"{name:<6s} {float(np.corrcoef(target, vals[:,idx])[0,1]):+.6f}")


if __name__ == "__main__":
    main()
