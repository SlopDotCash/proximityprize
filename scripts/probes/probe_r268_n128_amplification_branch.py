#!/usr/bin/env python3
"""#466 R268: n=128 amplified-moderate-ancestor branch.

R267 split n=128 coherent paths into inherited high-fine ancestors and a new
mode: moderate n=64 ancestors that become dangerous by a large top-level
coherent join.  This probe measures whether that second mode is captured by
simple amplification ratios such as X128 / X64best or fine128 / X64best.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r267_n128_ancestor_resonance_taxonomy import rows_for_m  # noqa: E402


@dataclass(frozen=True)
class Bucket:
    name: str
    count: int
    mass: float
    worst_mass: float
    worst_m: int
    worst_p: int
    worst_ratio: float


def summarize(name: str, rows: list) -> Bucket:
    if not rows:
        return Bucket(name, 0, 0.0, 0.0, 0, 0, 0.0)
    worst = max(rows, key=lambda row: row.mass128)
    return Bucket(
        name=name,
        count=len(rows),
        mass=sum(row.mass128 for row in rows),
        worst_mass=worst.mass128,
        worst_m=worst.m128,
        worst_p=worst.p,
        worst_ratio=worst.x128 / max(worst.x64, 1.0e-12),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--cos-floor", type=float, default=0.9)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--ratio-cuts", type=float, nargs="+", default=[1.25, 1.5, 1.75, 2.0])
    parser.add_argument("--fine-ratio-cuts", type=float, nargs="+", default=[0.5, 0.75, 1.0, 1.25])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
        if row.min_cos128_path >= args.cos_floor
    ]
    rows.sort(key=lambda row: row.mass128, reverse=True)
    inherited = [row for row in rows if row.fine64 >= args.ancestor_fine_cut or row.x64 >= args.ancestor_x_cut]
    moderate = [row for row in rows if row.fine64 < args.ancestor_fine_cut and row.x64 < args.ancestor_x_cut]

    print(
        f"R268 n=128 amplification branch rows={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] min_fine128={args.min_fine128} "
        f"ancestor_fine_cut={args.ancestor_fine_cut} ancestor_x_cut={args.ancestor_x_cut}"
    )
    print(
        f"mass total={sum(r.mass128 for r in rows):.8f} "
        f"inherited={sum(r.mass128 for r in inherited):.8f} moderate={sum(r.mass128 for r in moderate):.8f}"
    )

    buckets = [summarize("inherited", inherited), summarize("moderate", moderate)]
    for cut in args.ratio_cuts:
        buckets.append(summarize(f"moderate_ratio_ge_{cut}", [r for r in moderate if r.x128 / max(r.x64, 1.0e-12) >= cut]))
    for cut in args.fine_ratio_cuts:
        buckets.append(summarize(f"moderate_fineRatio_ge_{cut}", [r for r in moderate if r.fine128 / max(r.x64, 1.0e-12) >= cut]))

    print("\nbucket coverage")
    print("bucket                         count mass      worstMass worstM worstP ratio")
    print("-" * 96)
    for b in buckets:
        print(
            f"{b.name:<30s} {b.count:<5d} {b.mass:<9.6f} {b.worst_mass:<9.6f} "
            f"{b.worst_m:<6d} {b.worst_p:<7d} {b.worst_ratio:.4f}"
        )

    if rows:
        ratios = np.array([r.x128 / max(r.x64, 1.0e-12) for r in rows])
        fine_ratios = np.array([r.fine128 / max(r.x64, 1.0e-12) for r in rows])
        print("\nratio summary")
        print(
            f"ratio median={np.median(ratios):.6f} max={ratios.max():.6f} "
            f"fineRatio median={np.median(fine_ratios):.6f} max={fine_ratios.max():.6f}"
        )

    print("\nworst moderate rows")
    print("mass      X128   X64    F128   F64    ratio  fRatio mgf128 mgf64  M      p       idx128 idx64")
    print("-" * 116)
    for row in moderate[: args.top]:
        ratio = row.x128 / max(row.x64, 1.0e-12)
        fine_ratio = row.fine128 / max(row.x64, 1.0e-12)
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.x64:<6.2f} {row.fine128:<6.2f} "
            f"{row.fine64:<6.2f} {ratio:<6.3f} {fine_ratio:<6.3f} "
            f"{row.mgf128:<6.3f} {row.mgf64:<6.3f} {row.m128:<6d} {row.p:<7d} "
            f"{row.index128:<6d} {row.index64}"
        )


if __name__ == "__main__":
    main()
