#!/usr/bin/env python3
"""#466 R287: envelope test for the n=128 moderate high-fineRatio branch.

R286 strengthened the low-fineRatio split: after the finite row `p=231169`,
low-ratio moderate rows are individually tiny.  This probe attacks the
remaining moderate branch by asking whether high-fineRatio rows are captured by
a theorem-shaped top-child + aligned-tail envelope.
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
    worst_p: int = 0
    worst_m: int = 0

    def add(self, shape: TailShape) -> None:
        self.count += 1
        self.mass += shape.row.mass128
        if shape.row.mass128 > self.worst_mass:
            self.worst_mass = shape.row.mass128
            self.worst_p = shape.row.p
            self.worst_m = shape.row.m128


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


def ratio_label(cuts: list[float], value: float) -> str:
    lo = 0.0
    for hi in cuts:
        if value < hi:
            return f"[{lo:.2f},{hi:.2f})"
        lo = hi
    return f"[{lo:.2f},inf)"


def format_shape(shape: TailShape) -> str:
    row = shape.row
    return (
        f"{row.mass128:<10.8f} {row.fine_ratio:<7.4f} {row.x128:<7.3f} "
        f"{row.fine128:<7.3f} {shape.top_rank:<5d} {shape.tail_rank:<7d} "
        f"{shape.top_x:<7.3f} {shape.tail_x:<7.3f} {shape.tail_over_top:<8.4f} "
        f"{row.fine64best:<8.3f} {row.m128:<7d} {row.p:<9d} {row.index128}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--ratio-cuts", type=float, nargs="+", default=[0.75, 0.85, 0.9, 0.95])
    parser.add_argument("--high-ratio-cut", type=float, default=0.75)
    parser.add_argument("--top-rank-cuts", type=int, nargs="+", default=[1, 2, 4, 8, 16])
    parser.add_argument("--tail-x-cuts", type=float, nargs="+", default=[0.0, 2.0, 4.0, 6.0, 8.0])
    parser.add_argument("--tail-rank-cuts", type=int, nargs="+", default=[512, 1024, 2048, 4096, 8192])
    parser.add_argument("--top", type=int, default=32)
    parser.add_argument("--progress-every-primes", type=int, default=50)
    parser.add_argument("--progress-every-seconds", type=float, default=30.0)
    args = parser.parse_args()

    buckets: dict[str, Bucket] = defaultdict(Bucket)
    top_high: list[tuple[float, int, TailShape]] = []
    top_escape_top8: list[tuple[float, int, TailShape]] = []
    top_escape_tail2: list[tuple[float, int, TailShape]] = []
    top_escape_tail4: list[tuple[float, int, TailShape]] = []
    coverage: dict[tuple[int, float], Bucket] = defaultdict(Bucket)
    tail_rank_caps: dict[int, Bucket] = defaultdict(Bucket)

    t0 = time.time()
    last_progress = t0
    primes = candidates = moderate = high = 0
    high_mass = 0.0

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
            shape = tail_shape(row)
            buckets[ratio_label(args.ratio_cuts, row.fine_ratio)].add(shape)
            if row.fine_ratio < args.high_ratio_cut:
                continue
            high += 1
            high_mass += row.mass128
            update_top(top_high, shape, args.top)
            if shape.top_rank > 8:
                update_top(top_escape_top8, shape, args.top)
            if shape.tail_x < 2.0:
                update_top(top_escape_tail2, shape, args.top)
            if shape.tail_x < 4.0:
                update_top(top_escape_tail4, shape, args.top)
            for top_cut in args.top_rank_cuts:
                for tail_cut in args.tail_x_cuts:
                    if shape.top_rank <= top_cut and shape.tail_x >= tail_cut:
                        coverage[(top_cut, tail_cut)].add(shape)
            for rank_cut in args.tail_rank_cuts:
                if shape.tail_rank <= rank_cut:
                    tail_rank_caps[rank_cut].add(shape)

        now = time.time()
        if (
            args.progress_every_primes > 0
            and primes % args.progress_every_primes == 0
            and primes > 0
        ) or now - last_progress >= args.progress_every_seconds:
            print(
                f"progress M={m128} primes={primes} rows={candidates} moderate={moderate} "
                f"high={high} highMass={high_mass:.8f} elapsed={now - t0:.1f}s",
                flush=True,
            )
            last_progress = now

    print(
        f"\nR287 n=128 high-fineRatio envelope M=[{args.min_index},{args.max_index}] "
        f"highRatio>={args.high_ratio_cut}"
    )
    print(
        f"primes={primes} candidateRows={candidates} moderateRows={moderate} "
        f"highRows={high} highMass={high_mass:.8f}"
    )

    print("\nfineRatio buckets over all moderate rows")
    print("bucket       count mass      worstMass worstM worstP")
    print("-" * 72)
    for label in sorted(buckets):
        bucket = buckets[label]
        print(
            f"{label:<12s} {bucket.count:<5d} {bucket.mass:<9.6f} "
            f"{bucket.worst_mass:<9.6f} {bucket.worst_m:<6d} {bucket.worst_p}"
        )

    print("\nhigh-branch coverage by top rank and tail value")
    print("topCut tailCut count mass      missingMass worstMass worstM worstP")
    print("-" * 88)
    for top_cut in args.top_rank_cuts:
        for tail_cut in args.tail_x_cuts:
            bucket = coverage[(top_cut, tail_cut)]
            print(
                f"{top_cut:<6d} {tail_cut:<7.2f} {bucket.count:<5d} {bucket.mass:<9.6f} "
                f"{high_mass - bucket.mass:<11.6f} {bucket.worst_mass:<9.6f} "
                f"{bucket.worst_m:<6d} {bucket.worst_p}"
            )

    print("\nhigh-branch coverage by tail rank cap")
    print("tailRank<= count mass      missingMass worstMass worstM worstP")
    print("-" * 76)
    for rank_cut in args.tail_rank_cuts:
        bucket = tail_rank_caps[rank_cut]
        print(
            f"{rank_cut:<10d} {bucket.count:<5d} {bucket.mass:<9.6f} "
            f"{high_mass - bucket.mass:<11.6f} {bucket.worst_mass:<9.6f} "
            f"{bucket.worst_m:<6d} {bucket.worst_p}"
        )

    for title, heap in [
        ("worst high-fineRatio rows", top_high),
        ("worst high rows escaping topRank<=8", top_escape_top8),
        ("worst high rows with tailX<2", top_escape_tail2),
        ("worst high rows with tailX<4", top_escape_tail4),
    ]:
        print(f"\n{title}")
        print("mass       fRatio  X128    F128    topR  tailR   topX    tailX   tail/top F64best  M       p         idx")
        print("-" * 118)
        for _, _, shape in sorted(heap, reverse=True):
            print(format_shape(shape))


if __name__ == "__main__":
    main()
