#!/usr/bin/env python3
"""#466 R266: micro-band cap by quotient-index windows.

R251 showed the R249 split has comfortable slack for a small uncached extension
past M=4096.  R266 profiles the direct micro-band score by M-window to see
whether the obstruction is a finite medium-index phenomenon.
"""

from __future__ import annotations

import argparse
import math
import sys
from collections import defaultdict
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import cached_desc  # noqa: E402


def bucket_of(m: int, width: int) -> tuple[int, int]:
    lo = ((m - 1) // width) * width + 1
    return lo, lo + width - 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=5000)
    parser.add_argument("--bucket-width", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--micro-cutoff", type=float, default=0.755)
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()

    rows = []
    skipped = 0
    for n in args.ns:
        for m in range(args.min_index, args.max_index + 1):
            p = m * n + 1
            if not is_prime(p):
                continue
            cached = cached_desc(p, n, args.chunk, args.cache_dir, args.cache_only)
            if cached is None:
                skipped += 1
                continue
            _xs, desc = cached
            residual = desc[min(args.trim, len(desc)) :]
            s = int(np.count_nonzero(residual >= args.theta)) / m
            micro = s * math.exp(args.micro_cutoff / 2.0)
            rows.append((micro, s, n, p, m))

    by_bucket = defaultdict(list)
    by_n_bucket = defaultdict(list)
    for row in rows:
        micro, _s, n, _p, m = row
        b = bucket_of(m, args.bucket_width)
        by_bucket[b].append(row)
        by_n_bucket[(n, b)].append(row)

    print(
        f"R266 micro-band index windows cases={len(rows)} skipped={skipped} "
        f"theta={args.theta} target={args.target_c}"
    )
    print("\noverall worst rows")
    print("micro    slack    S        n     p          M")
    print("-" * 72)
    for micro, s, n, p, m in sorted(rows, reverse=True)[: args.top]:
        print(f"{micro:<8.6f} {args.target_c-micro:<8.6f} {s:<8.6f} {n:<5d} {p:<10d} {m}")

    print("\nby M bucket")
    print("bucket       cases  worst    slack    n     p          M")
    print("-" * 86)
    for b in sorted(by_bucket):
        vals = sorted(by_bucket[b], reverse=True)
        micro, _s, n, p, m = vals[0]
        print(
            f"{b[0]:04d}-{b[1]:04d} {len(vals):<6d} {micro:<8.6f} "
            f"{args.target_c-micro:<8.6f} {n:<5d} {p:<10d} {m}"
        )

    print("\nby n and M bucket")
    print("n     bucket       cases  worst    slack    p          M")
    print("-" * 86)
    for key in sorted(by_n_bucket):
        n, b = key
        vals = sorted(by_n_bucket[key], reverse=True)
        micro, _s, _n, p, m = vals[0]
        print(
            f"{n:<5d} {b[0]:04d}-{b[1]:04d} {len(vals):<6d} {micro:<8.6f} "
            f"{args.target_c-micro:<8.6f} {p:<10d} {m}"
        )


if __name__ == "__main__":
    main()
