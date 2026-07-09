#!/usr/bin/env python3
"""#466 R291: moving tail-rank caps for the n=128 high-fineRatio shoulder.

R290 showed that a fixed `tailRank <= 8192` cap leaves a small but growing
boundary layer in `M=20001..30000`.  This probe compares fixed and moving caps
on the same scan to determine whether the boundary is an artifact of using a
constant rank cutoff.
"""

from __future__ import annotations

import argparse
import heapq
import math
import sys
import time
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r270_n128_oriented_child_rank import (  # noqa: E402
    RankRow,
    rank_rows_for_m,
)


@dataclass(frozen=True)
class TailShape:
    row: RankRow
    top_rank: int
    tail_rank: int
    top_x: float
    tail_x: float
    tail_over_top: float


@dataclass
class ResidualSummary:
    count: int = 0
    mass: float = 0.0
    worst_mass: float = 0.0
    worst_m: int = 0
    worst_p: int = 0
    max_tail_x: float = 0.0
    max_fine_ratio: float = 0.0
    max_top_rank: int = 0
    max_tail_rank: int = 0

    def add(self, shape: TailShape) -> None:
        row = shape.row
        self.count += 1
        self.mass += row.mass128
        if row.mass128 > self.worst_mass:
            self.worst_mass = row.mass128
            self.worst_m = row.m128
            self.worst_p = row.p
        self.max_tail_x = max(self.max_tail_x, shape.tail_x)
        self.max_fine_ratio = max(self.max_fine_ratio, row.fine_ratio)
        self.max_top_rank = max(self.max_top_rank, shape.top_rank)
        self.max_tail_rank = max(self.max_tail_rank, shape.tail_rank)


def is_moderate(row: RankRow, ancestor_fine_cut: float, ancestor_x_cut: float) -> bool:
    return row.fine64best < ancestor_fine_cut and max(row.x64a, row.x64b) < ancestor_x_cut


def tail_shape(row: RankRow) -> TailShape:
    if row.rank_a <= row.rank_b:
        top_rank, tail_rank = row.rank_a, row.rank_b
        top_x, tail_x = row.x64a, row.x64b
    else:
        top_rank, tail_rank = row.rank_b, row.rank_a
        top_x, tail_x = row.x64b, row.x64a
    return TailShape(
        row=row,
        top_rank=top_rank,
        tail_rank=tail_rank,
        top_x=top_x,
        tail_x=tail_x,
        tail_over_top=tail_x / max(top_x, 1.0e-12),
    )


def cap_value(name: str, m128: int) -> int:
    if name.startswith("fixed:"):
        return int(name.split(":", 1)[1])
    if name == "m/2":
        return m128 // 2
    if name == "m/3":
        return m128 // 3
    if name == "m/4":
        return m128 // 4
    if name.startswith("sqrt:"):
        c = float(name.split(":", 1)[1])
        return int(c * math.sqrt(m128))
    raise ValueError(f"unknown cap {name!r}")


def update_top(heap: list[tuple[float, int, str, TailShape]], label: str, shape: TailShape, limit: int) -> None:
    item = (shape.row.mass128, shape.row.p, label, shape)
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif item[0] > heap[0][0]:
        heapq.heapreplace(heap, item)


def format_shape(label: str, shape: TailShape) -> str:
    row = shape.row
    return (
        f"{label:<10s} {row.mass128:<10.8f} {row.fine_ratio:<7.4f} {row.x128:<7.3f} "
        f"{row.fine128:<7.3f} {shape.top_rank:<6d} {shape.tail_rank:<8d} "
        f"{shape.top_x:<7.3f} {shape.tail_x:<7.3f} {shape.tail_over_top:<8.4f} "
        f"{row.m128:<7d} {row.p:<9d} {row.index128}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=20001)
    parser.add_argument("--max-index", type=int, default=30000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--high-ratio-cut", type=float, default=0.75)
    parser.add_argument(
        "--caps",
        nargs="+",
        default=["fixed:8192", "fixed:12000", "fixed:16384", "m/4", "m/3", "m/2"],
    )
    parser.add_argument("--top", type=int, default=32)
    parser.add_argument("--progress-every-primes", type=int, default=120)
    parser.add_argument("--progress-every-seconds", type=float, default=30.0)
    args = parser.parse_args()

    summaries: dict[str, ResidualSummary] = defaultdict(ResidualSummary)
    top_rows: list[tuple[float, int, str, TailShape]] = []
    primes = candidates = moderate = high = 0
    high_mass = 0.0
    t0 = time.time()
    last_progress = t0

    for m128 in range(args.min_index, args.max_index + 1):
        p = 128 * m128 + 1
        if not is_prime(p):
            continue
        primes += 1
        rows = rank_rows_for_m(m128, args.chunk, args.top_per_row, args.min_fine128)
        candidates += len(rows)
        for row in rows:
            if not is_moderate(row, args.ancestor_fine_cut, args.ancestor_x_cut):
                continue
            moderate += 1
            if row.fine_ratio < args.high_ratio_cut:
                continue
            high += 1
            high_mass += row.mass128
            shape = tail_shape(row)
            for cap in args.caps:
                if shape.tail_rank > cap_value(cap, row.m128):
                    summaries[cap].add(shape)
                    update_top(top_rows, cap, shape, args.top)

        now = time.time()
        if (
            args.progress_every_primes > 0
            and primes % args.progress_every_primes == 0
            and primes > 0
        ) or now - last_progress >= args.progress_every_seconds:
            residual_bits = " ".join(f"{cap}:{summaries[cap].mass:.4f}" for cap in args.caps)
            print(
                f"progress M={m128} primes={primes} high={high} highMass={high_mass:.6f} "
                f"{residual_bits} elapsed={now - t0:.1f}s",
                flush=True,
            )
            last_progress = now

    print(
        f"\nR291 n=128 moving tail-rank caps M=[{args.min_index},{args.max_index}] "
        f"highRatio>={args.high_ratio_cut}"
    )
    print(
        f"primes={primes} candidateRows={candidates} moderateRows={moderate} "
        f"highRows={high} highMass={high_mass:.8f}"
    )

    print("\nresidual by cap")
    print("cap        count mass      share     worstMass worstM worstP maxTailX maxFR   maxTopR maxTailR")
    print("-" * 112)
    for cap in args.caps:
        s = summaries[cap]
        print(
            f"{cap:<10s} {s.count:<5d} {s.mass:<9.6f} "
            f"{(s.mass / high_mass if high_mass else 0.0):<9.6f} {s.worst_mass:<9.6f} "
            f"{s.worst_m:<6d} {s.worst_p:<8d} {s.max_tail_x:<8.4f} "
            f"{s.max_fine_ratio:<7.4f} {s.max_top_rank:<7d} {s.max_tail_rank}"
        )

    print("\nworst residual rows across caps")
    print("cap        mass       fRatio  X128    F128    topR   tailR    topX    tailX   tail/top M       p         idx")
    print("-" * 126)
    for _, _, cap, shape in sorted(top_rows, reverse=True):
        print(format_shape(cap, shape))


if __name__ == "__main__":
    main()
