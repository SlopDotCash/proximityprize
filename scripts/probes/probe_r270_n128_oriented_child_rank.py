#!/usr/bin/env python3
"""#466 R270: rank signature of n=128 oriented near-doubling joins.

R269 found that the near-doubling branch is an oriented same-phase join, not a
balanced-annulus event.  This probe asks whether the local event is countable by
rank: do the two n=64 children both lie among the top n=64 values, or can a
low-rank child produce the dangerous amplification?
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r269_n128_near_doubling_geometry import rows_for_m  # noqa: E402


@dataclass(frozen=True)
class RankRow:
    p: int
    m128: int
    index128: int
    mass128: float
    x128: float
    fine128: float
    x64a: float
    x64b: float
    rank_a: int
    rank_b: int
    best_rank: int
    worst_rank: int
    balance: float
    fine_ratio: float
    fine64best: float


def rank_rows_for_m(m128: int, chunk: int, top: int, min_fine128: float) -> list[RankRow]:
    rows = rows_for_m(m128, chunk, top, min_fine128)
    if not rows:
        return []
    xvals = []
    # Reconstruct the n=64 child values from the rows only for the parent pairs is
    # not enough to rank globally, so import the raw helper through rows_for_m's
    # module would be circular-ish.  Instead recompute x64 cheaply via the first
    # row's module-level implementation by delegating to R269's local row data is
    # intentionally avoided; use numpy ranks over all child values below.
    from scripts.probes.probe_r269_n128_near_doubling_geometry import raw_periods, normalized

    p = 128 * m128 + 1
    eta64 = raw_periods(p, 64, chunk)
    x64 = normalized(eta64, p, 64)
    order = np.argsort(x64)[::-1]
    ranks = np.empty(len(x64), dtype=np.int64)
    for rank, idx in enumerate(order, start=1):
        ranks[idx] = rank
    out: list[RankRow] = []
    m64 = len(x64)
    for row in rows:
        j64a = row.index128 % m64
        j64b = (row.index128 + m128) % m64
        rank_a = int(ranks[j64a])
        rank_b = int(ranks[j64b])
        out.append(
            RankRow(
                p=row.p,
                m128=row.m128,
                index128=row.index128,
                mass128=row.mass128,
                x128=row.x128,
                fine128=row.fine128,
                x64a=row.x64a,
                x64b=row.x64b,
                rank_a=rank_a,
                rank_b=rank_b,
                best_rank=min(rank_a, rank_b),
                worst_rank=max(rank_a, rank_b),
                balance=row.balance,
                fine_ratio=row.fine_ratio,
                fine64best=row.fine64best,
            )
        )
    return out


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
    parser.add_argument("--rank-cuts", type=int, nargs="+", default=[4, 8, 16, 32, 64, 128])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rank_rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    near = [
        row
        for row in rows
        if row.fine64best < args.ancestor_fine_cut
        and max(row.x64a, row.x64b) < args.ancestor_x_cut
        and row.fine_ratio >= args.fine_ratio_cut
    ]
    near.sort(key=lambda row: row.mass128, reverse=True)

    print(
        f"R270 n=128 oriented child rank rows={len(rows)} near={len(near)} "
        f"M=[{args.min_index},{args.max_index}] fine_ratio_cut={args.fine_ratio_cut}"
    )
    print(f"near_mass={sum(r.mass128 for r in near):.8f}")
    if near:
        print(
            f"bestRank median={float(np.median([r.best_rank for r in near])):.2f} "
            f"worstRank median={float(np.median([r.worst_rank for r in near])):.2f} "
            f"maxWorstRank={max(r.worst_rank for r in near)}"
        )

    print("\nrank-window coverage")
    print("cut  both<=cut count mass      worstMass worstM worstP")
    print("-" * 76)
    for cut in args.rank_cuts:
        cap = [row for row in near if row.worst_rank <= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"{cut:<4d} {len(cap):<9d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )

    print("\nworst near rows")
    print("mass      X128   F128   A64    B64    rA    rB    worstR fRatio bal    F64best M      p")
    print("-" * 116)
    for row in near[: args.top]:
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.fine128:<6.2f} {row.x64a:<6.2f} "
            f"{row.x64b:<6.2f} {row.rank_a:<5d} {row.rank_b:<5d} {row.worst_rank:<6d} "
            f"{row.fine_ratio:<6.3f} {row.balance:<6.3f} {row.fine64best:<7.2f} "
            f"{row.m128:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
