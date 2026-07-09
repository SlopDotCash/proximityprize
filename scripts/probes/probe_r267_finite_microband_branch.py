#!/usr/bin/env python3
"""#466 R267: finite branch for the direct micro-band cap.

R266 suggests splitting the direct micro-band theorem at M0=1536.  This probe
enumerates the finite branch M < M0 and reports all rows near the cap.
"""

from __future__ import annotations

import argparse
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
    parser.add_argument("--slack-threshold", type=float, default=0.02)
    parser.add_argument("--top", type=int, default=80)
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
            s = count / m
            micro = s * math.exp(args.micro_cutoff / 2.0)
            rows.append((micro, args.target_c - micro, count, s, n, p, m))

    rows.sort(reverse=True)
    near = [row for row in rows if row[1] <= args.slack_threshold]
    print(
        f"R267 finite micro-band branch cases={len(rows)} skipped={skipped} "
        f"M=[{args.min_index},{args.max_index_exclusive}) target={args.target_c}"
    )
    print(f"near_rows(slack<={args.slack_threshold})={len(near)}")
    print("micro    slack    count  S        n     p          M")
    print("-" * 82)
    for micro, slack, count, s, n, p, m in rows[: args.top]:
        marker = "*" if slack <= args.slack_threshold else " "
        print(f"{micro:<8.6f} {slack:<8.6f} {count:<6d} {s:<8.6f} {n:<5d} {p:<10d} {m} {marker}")

    print("\nby n summary")
    for n in args.ns:
        vals = [row for row in rows if row[4] == n]
        if not vals:
            continue
        best = vals[0]
        near_n = sum(1 for row in vals if row[1] <= args.slack_threshold)
        print(
            f"n={n} cases={len(vals)} near={near_n} "
            f"best_micro={best[0]:.8f} slack={best[1]:.8f} p={best[5]} M={best[6]}"
        )


if __name__ == "__main__":
    main()
