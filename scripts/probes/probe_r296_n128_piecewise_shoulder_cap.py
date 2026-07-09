#!/usr/bin/env python3
"""#466 R296: piecewise formula cap for the n=128 high-fineRatio shoulder.

R291--R295 found an empirical shoulder ladder for high-fineRatio moderate rows.
This probe turns that ladder into an executable cap formula and measures the
rows escaping it.
"""

from __future__ import annotations

import argparse
import heapq
import math
import sys
import time
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
    cap: int


@dataclass
class Summary:
    count: int = 0
    mass: float = 0.0
    worst_mass: float = 0.0
    worst_m: int = 0
    worst_p: int = 0
    max_tail_x: float = 0.0
    max_fine_ratio: float = 0.0
    max_top_rank: int = 0
    max_tail_rank: int = 0
    max_cap: int = 0

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
        self.max_cap = max(self.max_cap, shape.cap)


def is_moderate(row: RankRow, ancestor_fine_cut: float, ancestor_x_cut: float) -> bool:
    return row.fine64best < ancestor_fine_cut and max(row.x64a, row.x64b) < ancestor_x_cut


def shoulder_cap(m128: int, step: int, offset: int, minimum: int) -> int:
    return max(minimum, step * math.ceil((m128 + offset) / 15000.0))


def previous_cap(cap: int, step: int, minimum: int) -> int:
    return max(minimum, cap - step)


def tail_shape(row: RankRow, cap: int) -> TailShape:
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
        cap=cap,
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
        f"{shape.cap:<7d} {shape.top_x:<7.3f} {shape.tail_x:<7.3f} "
        f"{shape.tail_over_top:<8.4f} {row.m128:<7d} {row.p:<9d} {row.index128}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=12001)
    parser.add_argument("--max-index", type=int, default=80000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--high-ratio-cut", type=float, default=0.75)
    parser.add_argument("--step", type=int, default=8192)
    parser.add_argument("--offset", type=int, default=10000)
    parser.add_argument("--minimum", type=int, default=8192)
    parser.add_argument("--top", type=int, default=32)
    parser.add_argument("--progress-every-primes", type=int, default=120)
    parser.add_argument("--progress-every-seconds", type=float, default=30.0)
    args = parser.parse_args()

    formula = Summary()
    prev = Summary()
    formula_top: list[tuple[float, int, TailShape]] = []
    prev_top: list[tuple[float, int, TailShape]] = []
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
        cap = shoulder_cap(m128, args.step, args.offset, args.minimum)
        old_cap = previous_cap(cap, args.step, args.minimum)
        for row in rows:
            if not is_moderate(row, args.ancestor_fine_cut, args.ancestor_x_cut):
                continue
            moderate += 1
            if row.fine_ratio < args.high_ratio_cut:
                continue
            high += 1
            high_mass += row.mass128
            shape = tail_shape(row, cap)
            if shape.tail_rank > cap:
                formula.add(shape)
                update_top(formula_top, shape, args.top)
            if shape.tail_rank > old_cap:
                prev.add(shape)
                update_top(prev_top, shape, args.top)

        now = time.time()
        if (
            args.progress_every_primes > 0
            and primes % args.progress_every_primes == 0
            and primes > 0
        ) or now - last_progress >= args.progress_every_seconds:
            print(
                f"progress M={m128} primes={primes} high={high} highMass={high_mass:.6f} "
                f"formulaMass={formula.mass:.6f} prevMass={prev.mass:.6f} cap={cap} "
                f"elapsed={now - t0:.1f}s",
                flush=True,
            )
            last_progress = now

    print(
        f"\nR296 n=128 piecewise shoulder cap M=[{args.min_index},{args.max_index}] "
        f"cap={args.step}*ceil((M+{args.offset})/15000)"
    )
    print(
        f"primes={primes} candidateRows={candidates} moderateRows={moderate} "
        f"highRows={high} highMass={high_mass:.8f}"
    )

    print("\nresidual summary")
    print("kind       count mass      share     worstMass worstM worstP maxTailX maxFR   maxTopR maxTailR maxCap")
    print("-" * 116)
    for name, summary in [("formula", formula), ("prevCap", prev)]:
        print(
            f"{name:<10s} {summary.count:<5d} {summary.mass:<9.6f} "
            f"{(summary.mass / high_mass if high_mass else 0.0):<9.6f} "
            f"{summary.worst_mass:<9.6f} {summary.worst_m:<6d} {summary.worst_p:<8d} "
            f"{summary.max_tail_x:<8.4f} {summary.max_fine_ratio:<7.4f} "
            f"{summary.max_top_rank:<7d} {summary.max_tail_rank:<8d} {summary.max_cap}"
        )

    for title, heap in [("worst formula escapes", formula_top), ("worst previous-cap escapes", prev_top)]:
        print(f"\n{title}")
        print("mass       fRatio  X128    F128    topR   tailR    cap     topX    tailX   tail/top M       p         idx")
        print("-" * 128)
        for _, _, shape in sorted(heap, reverse=True):
            print(format_shape(shape))


if __name__ == "__main__":
    main()
