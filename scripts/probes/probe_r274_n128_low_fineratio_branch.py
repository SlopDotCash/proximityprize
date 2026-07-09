#!/usr/bin/env python3
"""#466 R274: n=128 moderate low-fineRatio branch.

R273 showed that a high fineRatio top-tail certificate misses the largest
moderate row, p=231169.  This probe isolates the moderate low-fineRatio branch
and asks whether it is a small finite family or a stable third mode.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r270_n128_oriented_child_rank import rank_rows_for_m  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--bands", type=float, nargs="+", default=[0.75, 0.85, 0.9, 0.95])
    parser.add_argument("--top", type=int, default=40)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rank_rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    moderate = [
        row
        for row in rows
        if row.fine64best < args.ancestor_fine_cut and max(row.x64a, row.x64b) < args.ancestor_x_cut
    ]
    moderate.sort(key=lambda row: row.mass128, reverse=True)

    print(
        f"R274 n=128 low-fineRatio branch rows={len(rows)} moderate={len(moderate)} "
        f"M=[{args.min_index},{args.max_index}]"
    )
    print(f"moderate_mass={sum(r.mass128 for r in moderate):.8f}")

    cuts = [0.0] + args.bands + [float("inf")]
    print("\nfineRatio bands")
    print("band             count mass      worstMass worstM worstP medianBestRank medianWorstRank")
    print("-" * 104)
    for lo, hi in zip(cuts, cuts[1:]):
        band = [r for r in moderate if lo <= r.fine_ratio < hi]
        worst = max(band, key=lambda r: r.mass128) if band else None
        label_hi = "inf" if hi == float("inf") else f"{hi:.2f}"
        if band:
            med_best = float(np.median([r.best_rank for r in band]))
            med_worst = float(np.median([r.worst_rank for r in band]))
        else:
            med_best = med_worst = 0.0
        print(
            f"[{lo:.2f},{label_hi})     {len(band):<5d} {sum(r.mass128 for r in band):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0):<7d} {med_best:<14.2f} {med_worst:<.2f}"
        )

    low = [r for r in moderate if r.fine_ratio < args.bands[0]]
    primes = Counter(r.p for r in low)
    print("\nlow-band prime concentration")
    for p, count in primes.most_common(12):
        mass = sum(r.mass128 for r in low if r.p == p)
        ms = sorted({r.m128 for r in low if r.p == p})
        print(f"p={p:<8d} count={count:<3d} mass={mass:.8f} M={','.join(map(str, ms[:8]))}")

    print("\nworst low-band rows")
    print("mass      fRatio X128   F128   X64max F64best bestR worstR M      p       idx")
    print("-" * 108)
    for r in low[: args.top]:
        print(
            f"{r.mass128:<9.6f} {r.fine_ratio:<6.3f} {r.x128:<6.2f} {r.fine128:<6.2f} "
            f"{max(r.x64a,r.x64b):<6.2f} {r.fine64best:<7.2f} {r.best_rank:<5d} "
            f"{r.worst_rank:<6d} {r.m128:<6d} {r.p:<7d} {r.index128}"
        )


if __name__ == "__main__":
    main()
