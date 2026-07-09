#!/usr/bin/env python3
"""#466 R288: residual beyond the n=128 high-fineRatio tail-rank shoulder.

R287 refuted a top-rank-only certificate for the moderate high-fineRatio branch,
but found that `tailRank <= 8192` captured almost all high-branch mass in the
continuation window.  This probe isolates the complementary residual and asks
whether it is a tiny-tail, rowwise-small event.
"""

from __future__ import annotations

import argparse
import heapq
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
class Bucket:
    count: int = 0
    mass: float = 0.0
    worst_mass: float = 0.0
    worst_m: int = 0
    worst_p: int = 0

    def add(self, shape: TailShape) -> None:
        row = shape.row
        self.count += 1
        self.mass += row.mass128
        if row.mass128 > self.worst_mass:
            self.worst_mass = row.mass128
            self.worst_m = row.m128
            self.worst_p = row.p


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


def update_top(heap: list[tuple[float, int, TailShape]], shape: TailShape, limit: int) -> None:
    item = (shape.row.mass128, shape.row.p, shape)
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif item[0] > heap[0][0]:
        heapq.heapreplace(heap, item)


def format_shape(shape: TailShape) -> str:
    row = shape.row
    return (
        f"{row.mass128:<10.8f} {row.fine_ratio:<7.4f} {row.x128:<7.3f} "
        f"{row.fine128:<7.3f} {shape.top_rank:<6d} {shape.tail_rank:<8d} "
        f"{shape.top_x:<7.3f} {shape.tail_x:<7.3f} {shape.tail_over_top:<8.4f} "
        f"{row.fine64best:<8.3f} {row.m128:<7d} {row.p:<9d} {row.index128}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=12001)
    parser.add_argument("--max-index", type=int, default=20000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--high-ratio-cut", type=float, default=0.75)
    parser.add_argument("--tail-rank-cap", type=int, default=8192)
    parser.add_argument("--tail-x-cuts", type=float, nargs="+", default=[1.0, 2.0, 3.0, 4.0, 6.0])
    parser.add_argument("--ratio-cuts", type=float, nargs="+", default=[0.8, 0.85, 0.9, 0.95, 0.99])
    parser.add_argument("--top-rank-cuts", type=int, nargs="+", default=[4, 8, 16, 32, 64])
    parser.add_argument("--top", type=int, default=32)
    parser.add_argument("--progress-every-primes", type=int, default=100)
    parser.add_argument("--progress-every-seconds", type=float, default=30.0)
    args = parser.parse_args()

    residual_by_tail_x: dict[float, Bucket] = defaultdict(Bucket)
    residual_by_ratio: dict[float, Bucket] = defaultdict(Bucket)
    residual_by_top_rank: dict[int, Bucket] = defaultdict(Bucket)
    residual_top: list[tuple[float, int, TailShape]] = []
    residual = high = moderate = candidates = primes = 0
    high_mass = residual_mass = 0.0
    max_tail_x = 0.0
    max_top_rank = max_tail_rank = 0
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
            if shape.tail_rank <= args.tail_rank_cap:
                continue
            residual += 1
            residual_mass += row.mass128
            max_tail_x = max(max_tail_x, shape.tail_x)
            max_top_rank = max(max_top_rank, shape.top_rank)
            max_tail_rank = max(max_tail_rank, shape.tail_rank)
            update_top(residual_top, shape, args.top)
            for cut in args.tail_x_cuts:
                if shape.tail_x < cut:
                    residual_by_tail_x[cut].add(shape)
            for cut in args.ratio_cuts:
                if row.fine_ratio >= cut:
                    residual_by_ratio[cut].add(shape)
            for cut in args.top_rank_cuts:
                if shape.top_rank <= cut:
                    residual_by_top_rank[cut].add(shape)

        now = time.time()
        if (
            args.progress_every_primes > 0
            and primes % args.progress_every_primes == 0
            and primes > 0
        ) or now - last_progress >= args.progress_every_seconds:
            print(
                f"progress M={m128} primes={primes} high={high} residual={residual} "
                f"resMass={residual_mass:.8f} elapsed={now - t0:.1f}s",
                flush=True,
            )
            last_progress = now

    print(
        f"\nR288 n=128 high-fineRatio tail-rank residual M=[{args.min_index},{args.max_index}] "
        f"tailRank>{args.tail_rank_cap}"
    )
    print(
        f"primes={primes} candidateRows={candidates} moderateRows={moderate} highRows={high} "
        f"highMass={high_mass:.8f}"
    )
    print(
        f"residualRows={residual} residualMass={residual_mass:.8f} "
        f"residualShare={(residual_mass / high_mass if high_mass else 0.0):.8f} "
        f"maxTailX={max_tail_x:.6f} maxTopRank={max_top_rank} maxTailRank={max_tail_rank}"
    )

    print("\nresidual tail-x sublevel coverage")
    print("tailX< count mass      share     worstMass worstM worstP")
    print("-" * 76)
    for cut in args.tail_x_cuts:
        bucket = residual_by_tail_x[cut]
        print(
            f"{cut:<7.2f} {bucket.count:<5d} {bucket.mass:<9.6f} "
            f"{(bucket.mass / residual_mass if residual_mass else 0.0):<9.6f} "
            f"{bucket.worst_mass:<9.6f} {bucket.worst_m:<6d} {bucket.worst_p}"
        )

    print("\nresidual high-ratio thresholds")
    print("fineRatio>= count mass      share     worstMass worstM worstP")
    print("-" * 82)
    for cut in args.ratio_cuts:
        bucket = residual_by_ratio[cut]
        print(
            f"{cut:<11.2f} {bucket.count:<5d} {bucket.mass:<9.6f} "
            f"{(bucket.mass / residual_mass if residual_mass else 0.0):<9.6f} "
            f"{bucket.worst_mass:<9.6f} {bucket.worst_m:<6d} {bucket.worst_p}"
        )

    print("\nresidual top-rank coverage")
    print("topRank<= count mass      share     worstMass worstM worstP")
    print("-" * 78)
    for cut in args.top_rank_cuts:
        bucket = residual_by_top_rank[cut]
        print(
            f"{cut:<9d} {bucket.count:<5d} {bucket.mass:<9.6f} "
            f"{(bucket.mass / residual_mass if residual_mass else 0.0):<9.6f} "
            f"{bucket.worst_mass:<9.6f} {bucket.worst_m:<6d} {bucket.worst_p}"
        )

    print("\nworst residual rows")
    print("mass       fRatio  X128    F128    topR   tailR    topX    tailX   tail/top F64best  M       p         idx")
    print("-" * 120)
    for _, _, shape in sorted(residual_top, reverse=True):
        print(format_shape(shape))


if __name__ == "__main__":
    main()
