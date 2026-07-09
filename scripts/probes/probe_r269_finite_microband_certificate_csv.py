#!/usr/bin/env python3
"""#466 R269: CSV certificate for the finite micro-band branch.

R267 shows the finite branch M < 1536 has only 465 rows.  This probe writes a
stable CSV certificate with the exact survivor counts for each row.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import cached_desc  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index-exclusive", type=int, default=1536)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--micro-cutoff", type=float, default=0.755)
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("docs/kb/data/deltastar-466-r269-finite-microband-certificate.csv"),
    )
    args = parser.parse_args()

    rows = []
    skipped = 0
    for n in args.ns:
        for m in range(args.min_index, args.max_index_exclusive):
            p = m * n + 1
            if not is_prime(p):
                continue
            cached = cached_desc(p, n, args.chunk, args.cache_dir, args.cache_only)
            if cached is None:
                skipped += 1
                continue
            _xs, desc = cached
            residual = desc[min(args.trim, len(desc)) :]
            count = int(np.count_nonzero(residual >= args.theta))
            survival = count / m
            micro = survival * math.exp(args.micro_cutoff / 2.0)
            rows.append(
                {
                    "n": n,
                    "p": p,
                    "M": m,
                    "trim": args.trim,
                    "theta": args.theta,
                    "count": count,
                    "survival": f"{survival:.12f}",
                    "micro_cost": f"{micro:.12f}",
                    "slack": f"{args.target_c - micro:.12f}",
                }
            )

    rows.sort(key=lambda r: (-float(r["micro_cost"]), r["n"], r["p"], r["M"]))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "n",
                "p",
                "M",
                "trim",
                "theta",
                "count",
                "survival",
                "micro_cost",
                "slack",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    print(
        f"R269 finite micro-band CSV rows={len(rows)} skipped={skipped} "
        f"out={args.out}"
    )
    if rows:
        best = rows[0]
        print(
            "best "
            f"n={best['n']} p={best['p']} M={best['M']} count={best['count']} "
            f"micro={best['micro_cost']} slack={best['slack']}"
        )


if __name__ == "__main__":
    main()
