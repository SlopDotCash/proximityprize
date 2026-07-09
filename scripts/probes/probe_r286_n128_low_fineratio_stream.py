#!/usr/bin/env python3
"""#466 R286: streaming stress test for the n=128 low-fineRatio branch.

R274 found that the moderate low-fineRatio branch was dominated by one row
(`p=231169`) on `M <= 12000`, with the remaining rows two orders of magnitude
smaller.  This continuation probe scans wider windows without retaining all
rows, reports progress, and keeps only the low-band leaderboard needed to test
whether a second large outlier appears.
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
class Summary:
    m_seen: int
    primes_seen: int
    candidate_rows: int
    moderate_rows: int
    low_rows: int
    low_mass: float
    low_mass_without_exceptions: float
    max_low_mass: float
    max_low_mass_without_exceptions: float


def is_moderate(row: RankRow, ancestor_fine_cut: float, ancestor_x_cut: float) -> bool:
    return row.fine64best < ancestor_fine_cut and max(row.x64a, row.x64b) < ancestor_x_cut


def update_top(heap: list[tuple[float, int, RankRow]], row: RankRow, limit: int) -> None:
    item = (row.mass128, row.p, row)
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif item[0] > heap[0][0]:
        heapq.heapreplace(heap, item)


def format_row(row: RankRow) -> str:
    return (
        f"{row.mass128:<10.8f} {row.fine_ratio:<7.4f} {row.x128:<7.3f} "
        f"{row.fine128:<7.3f} {max(row.x64a, row.x64b):<7.3f} "
        f"{row.fine64best:<8.3f} {row.best_rank:<6d} {row.worst_rank:<7d} "
        f"{row.m128:<7d} {row.p:<9d} {row.index128}"
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
    parser.add_argument("--fine-ratio-cut", type=float, default=0.75)
    parser.add_argument("--exclude-primes", type=int, nargs="*", default=[231169])
    parser.add_argument("--top", type=int, default=32)
    parser.add_argument("--max-primes", type=int, default=0)
    parser.add_argument("--progress-every-primes", type=int, default=5)
    parser.add_argument("--progress-every-seconds", type=float, default=30.0)
    args = parser.parse_args()

    exceptions = set(args.exclude_primes)
    top_heap: list[tuple[float, int, RankRow]] = []
    top_heap_without_exceptions: list[tuple[float, int, RankRow]] = []
    t0 = time.time()
    last_progress = t0
    m_seen = primes_seen = candidate_rows = moderate_rows = low_rows = 0
    low_mass = low_mass_without_exceptions = 0.0
    max_low_mass = max_low_mass_without_exceptions = 0.0

    for m128 in range(args.min_index, args.max_index + 1):
        m_seen += 1
        p = 128 * m128 + 1
        if not is_prime(p):
            continue
        primes_seen += 1
        rows = rank_rows_for_m(m128, args.chunk, args.top_per_row, args.min_fine128)
        candidate_rows += len(rows)
        for row in rows:
            if not is_moderate(row, args.ancestor_fine_cut, args.ancestor_x_cut):
                continue
            moderate_rows += 1
            if row.fine_ratio >= args.fine_ratio_cut:
                continue
            low_rows += 1
            low_mass += row.mass128
            max_low_mass = max(max_low_mass, row.mass128)
            update_top(top_heap, row, args.top)
            if row.p not in exceptions:
                low_mass_without_exceptions += row.mass128
                max_low_mass_without_exceptions = max(max_low_mass_without_exceptions, row.mass128)
                update_top(top_heap_without_exceptions, row, args.top)

        now = time.time()
        if (
            args.progress_every_primes > 0
            and primes_seen % args.progress_every_primes == 0
            and primes_seen > 0
        ) or now - last_progress >= args.progress_every_seconds:
            elapsed = now - t0
            print(
                f"progress M={m128} p={p} primes={primes_seen} rows={candidate_rows} "
                f"low={low_rows} lowMass={low_mass:.8f} "
                f"maxNoExc={max_low_mass_without_exceptions:.8f} elapsed={elapsed:.1f}s",
                flush=True,
            )
            last_progress = now

        if args.max_primes and primes_seen >= args.max_primes:
            break

    summary = Summary(
        m_seen=m_seen,
        primes_seen=primes_seen,
        candidate_rows=candidate_rows,
        moderate_rows=moderate_rows,
        low_rows=low_rows,
        low_mass=low_mass,
        low_mass_without_exceptions=low_mass_without_exceptions,
        max_low_mass=max_low_mass,
        max_low_mass_without_exceptions=max_low_mass_without_exceptions,
    )

    print(
        "\nR286 n=128 low-fineRatio stream "
        f"M=[{args.min_index},{args.min_index + summary.m_seen - 1}] "
        f"fineRatio<{args.fine_ratio_cut}"
    )
    print(
        f"primes={summary.primes_seen} candidateRows={summary.candidate_rows} "
        f"moderateRows={summary.moderate_rows} lowRows={summary.low_rows}"
    )
    print(
        f"lowMass={summary.low_mass:.8f} maxLowMass={summary.max_low_mass:.8f} "
        f"lowMassNoExceptions={summary.low_mass_without_exceptions:.8f} "
        f"maxLowMassNoExceptions={summary.max_low_mass_without_exceptions:.8f}"
    )

    print("\nworst low-band rows")
    print("mass       fRatio  X128    F128    X64max  F64best  bestR  worstR  M       p         idx")
    print("-" * 104)
    for _, _, row in sorted(top_heap, reverse=True):
        print(format_row(row))

    if exceptions:
        print("\nworst low-band rows excluding finite exceptions")
        print("mass       fRatio  X128    F128    X64max  F64best  bestR  worstR  M       p         idx")
        print("-" * 104)
        for _, _, row in sorted(top_heap_without_exceptions, reverse=True):
            print(format_row(row))


if __name__ == "__main__":
    main()
