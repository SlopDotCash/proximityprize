#!/usr/bin/env python3
"""#466 R271: top-child aligned-tail mass for n=128 joins.

R270 refuted the top-top collision certificate: dangerous near-doubling joins
are usually a top n=64 child plus a much lower-ranked aligned tail child.  This
probe measures the conditional tail around top children.  For each near branch
row it records the high child's rank and the lower child's rank/value, then
sweeps windows on the top-child rank and lower-child value/rank.
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
class TailRow:
    p: int
    m128: int
    mass128: float
    x128: float
    fine128: float
    top_rank: int
    tail_rank: int
    top_x64: float
    tail_x64: float
    tail_over_top: float
    fine_ratio: float
    fine64best: float


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--fine-ratio-cut", type=float, default=0.75)
    parser.add_argument("--top-rank-cuts", type=int, nargs="+", default=[1, 2, 4, 8, 16])
    parser.add_argument("--tail-rank-cuts", type=int, nargs="+", default=[32, 64, 128, 256, 512, 1024])
    parser.add_argument("--tail-x-cuts", type=float, nargs="+", default=[2.0, 4.0, 6.0, 8.0, 10.0])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rank_rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rank_rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    near = [
        row
        for row in rank_rows
        if row.fine64best < args.ancestor_fine_cut
        and max(row.x64a, row.x64b) < args.ancestor_x_cut
        and row.fine_ratio >= args.fine_ratio_cut
    ]
    rows: list[TailRow] = []
    for row in near:
        if row.rank_a <= row.rank_b:
            top_rank, tail_rank = row.rank_a, row.rank_b
            top_x, tail_x = row.x64a, row.x64b
        else:
            top_rank, tail_rank = row.rank_b, row.rank_a
            top_x, tail_x = row.x64b, row.x64a
        rows.append(
            TailRow(
                p=row.p,
                m128=row.m128,
                mass128=row.mass128,
                x128=row.x128,
                fine128=row.fine128,
                top_rank=top_rank,
                tail_rank=tail_rank,
                top_x64=top_x,
                tail_x64=tail_x,
                tail_over_top=tail_x / max(top_x, 1.0e-12),
                fine_ratio=row.fine_ratio,
                fine64best=row.fine64best,
            )
        )
    rows.sort(key=lambda row: row.mass128, reverse=True)

    print(
        f"R271 n=128 tail-around-spike rows={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] fine_ratio_cut={args.fine_ratio_cut}"
    )
    print(f"total_mass={sum(r.mass128 for r in rows):.8f}")
    if rows:
        print(
            f"topRank median={float(np.median([r.top_rank for r in rows])):.2f} "
            f"tailRank median={float(np.median([r.tail_rank for r in rows])):.2f} "
            f"tailX median={float(np.median([r.tail_x64 for r in rows])):.6f} "
            f"tail/top median={float(np.median([r.tail_over_top for r in rows])):.6f}"
        )

    print("\ncoverage by top rank and tail thresholds")
    print("condition             count mass      worstMass worstM worstP")
    print("-" * 86)
    for cut in args.top_rank_cuts:
        cap = [row for row in rows if row.top_rank <= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"topRank<={cut:<6d} {len(cap):<5d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )
    for cut in args.tail_rank_cuts:
        cap = [row for row in rows if row.tail_rank <= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"tailRank<={cut:<5d} {len(cap):<5d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )
    for cut in args.tail_x_cuts:
        cap = [row for row in rows if row.tail_x64 >= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"tailX>={cut:<8.2f} {len(cap):<5d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )

    print("\nworst rows")
    print("mass      X128   F128   topR tailR topX   tailX  tail/top fRatio F64best M      p")
    print("-" * 116)
    for row in rows[: args.top]:
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.fine128:<6.2f} "
            f"{row.top_rank:<4d} {row.tail_rank:<5d} {row.top_x64:<6.2f} "
            f"{row.tail_x64:<6.2f} {row.tail_over_top:<8.3f} {row.fine_ratio:<6.3f} "
            f"{row.fine64best:<7.2f} {row.m128:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
