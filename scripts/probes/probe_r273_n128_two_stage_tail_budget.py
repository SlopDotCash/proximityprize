#!/usr/bin/env python3
"""#466 R273: two-stage n=128 resonance + moderate tail budget.

R272 refuted a one-piece top-tail certificate because inherited resonance rows
pollute the top-tail mass.  This probe applies the intended two-stage split:

1. classify rows as inherited if the selected n=64 ancestor has large fine64
   or large X64;
2. on the remaining moderate rows, measure top-rank/tail-value/fine-ratio
   certificates.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r270_n128_oriented_child_rank import rank_rows_for_m  # noqa: E402


@dataclass(frozen=True)
class SplitSummary:
    name: str
    count: int
    mass: float
    worst_mass: float
    worst_m: int
    worst_p: int


def summarize(name: str, rows: list) -> SplitSummary:
    if not rows:
        return SplitSummary(name, 0, 0.0, 0.0, 0, 0)
    worst = max(rows, key=lambda row: row.mass128)
    return SplitSummary(name, len(rows), sum(row.mass128 for row in rows), worst.mass128, worst.m128, worst.p)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cuts", type=float, nargs="+", default=[6.0, 8.0, 10.0])
    parser.add_argument("--ancestor-x-cuts", type=float, nargs="+", default=[14.0, 16.0, 18.0])
    parser.add_argument("--top-rank-cuts", type=int, nargs="+", default=[4, 8, 16])
    parser.add_argument("--tail-x-cuts", type=float, nargs="+", default=[2.0, 4.0, 6.0])
    parser.add_argument("--fine-ratio-cuts", type=float, nargs="+", default=[0.75, 0.85, 0.9, 0.95])
    parser.add_argument("--top", type=int, default=25)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rank_rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    print(
        f"R273 n=128 two-stage tail budget rows={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] min_fine128={args.min_fine128}"
    )
    print(f"total_mass={sum(row.mass128 for row in rows):.8f}")

    summaries: list[SplitSummary] = []
    print("\nsplit grid")
    print("fineCut xCut inheritedMass moderateMass bestTailMass worstTailMass label")
    print("-" * 112)
    for fine_cut in args.ancestor_fine_cuts:
        for x_cut in args.ancestor_x_cuts:
            inherited = [row for row in rows if row.fine64best >= fine_cut or max(row.x64a, row.x64b) >= x_cut]
            moderate = [row for row in rows if row.fine64best < fine_cut and max(row.x64a, row.x64b) < x_cut]
            best_tail_mass = 0.0
            best_label = ""
            worst_tail_mass = 0.0
            for top_cut in args.top_rank_cuts:
                for tail_cut in args.tail_x_cuts:
                    for ratio_cut in args.fine_ratio_cuts:
                        cap = [
                            row
                            for row in moderate
                            if row.best_rank <= top_cut
                            and min(row.x64a, row.x64b) >= tail_cut
                            and row.fine_ratio >= ratio_cut
                        ]
                        mass = sum(row.mass128 for row in cap)
                        if best_label == "" or mass < best_tail_mass:
                            best_tail_mass = mass
                            best_label = f"top<={top_cut},tail>={tail_cut:.1f},fr>={ratio_cut:.2f}"
                        if mass > worst_tail_mass:
                            worst_tail_mass = mass
            summaries.append(summarize(f"inherited f{fine_cut} x{x_cut}", inherited))
            summaries.append(summarize(f"moderate f{fine_cut} x{x_cut}", moderate))
            print(
                f"{fine_cut:<7.1f} {x_cut:<4.1f} {sum(r.mass128 for r in inherited):<13.6f} "
                f"{sum(r.mass128 for r in moderate):<12.6f} {best_tail_mass:<12.6f} "
                f"{worst_tail_mass:<13.6f} {best_label}"
            )

    print("\ncomponent worst cases")
    print("component                     count mass      worstMass worstM worstP")
    print("-" * 92)
    summaries.sort(key=lambda s: s.mass, reverse=True)
    for s in summaries[: args.top]:
        print(f"{s.name:<29s} {s.count:<5d} {s.mass:<9.6f} {s.worst_mass:<9.6f} {s.worst_m:<6d} {s.worst_p}")

    # Print the actual worst rows that are moderate for the baseline split used in R268/R271.
    base_fine, base_x = 8.0, 16.0
    moderate = [
        row for row in rows if row.fine64best < base_fine and max(row.x64a, row.x64b) < base_x
    ]
    moderate.sort(key=lambda row: row.mass128, reverse=True)
    print("\nworst baseline moderate rows (fine64<8, x64<16)")
    print("mass      X128   F128   X64max F64best bestR worstR fRatio M      p")
    print("-" * 104)
    for row in moderate[: args.top]:
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.fine128:<6.2f} "
            f"{max(row.x64a,row.x64b):<6.2f} {row.fine64best:<7.2f} "
            f"{row.best_rank:<5d} {row.worst_rank:<6d} {row.fine_ratio:<6.3f} "
            f"{row.m128:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
