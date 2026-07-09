#!/usr/bin/env python3
"""#466 R251: stress-test the R249 trim-five split certificate.

R249 reduces the residual tail socket to two exact quantities:

    micro = S(0.75) * exp(0.755/2)
    tail  = sup_{theta >= 0.755} S(theta) * exp(theta/2)

both needing to be <= 0.6012 after deleting the top five quotient values.
This probe computes those quantities on exact spectra, optionally using the
R231 cache where available.
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


def split_stats(desc: np.ndarray, m: int, trim: int, tau: float, cutoff: float) -> tuple:
    residual = desc[min(trim, len(desc)) :]
    s_tau = int(np.count_nonzero(residual >= tau)) / m
    micro = s_tau * math.exp(cutoff / 2.0)
    best_tail = (0.0, cutoff, 0)
    for idx, x0 in enumerate(residual, start=1):
        theta = float(x0)
        if theta < cutoff:
            break
        h = (idx / m) * math.exp(theta / 2.0)
        if h > best_tail[0]:
            best_tail = (h, theta, idx)
    return micro, s_tau, best_tail


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[128, 256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=8192)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--tau", type=float, default=0.75)
    parser.add_argument("--cutoff", type=float, default=0.755)
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument("--top", type=int, default=30)
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
            micro, s_tau, (tail, tail_theta, tail_count) = split_stats(
                desc, m, args.trim, args.tau, args.cutoff
            )
            rows.append(
                (
                    max(micro, tail),
                    micro,
                    tail,
                    s_tau,
                    tail_theta,
                    tail_count,
                    n,
                    p,
                    m,
                )
            )

    rows.sort(reverse=True)
    print(
        f"R251 R249 split stress cases={len(rows)} skipped={skipped} "
        f"trim={args.trim} tau={args.tau} cutoff={args.cutoff} target={args.target_c}"
    )
    print("worst    slack    micro    tail     S_tau    tailTheta count  n     p          M")
    print("-" * 112)
    for worst, micro, tail, s_tau, tail_theta, tail_count, n, p, m in rows[: args.top]:
        print(
            f"{worst:<8.6f} {args.target_c-worst:<8.6f} {micro:<8.6f} {tail:<8.6f} "
            f"{s_tau:<8.6f} {tail_theta:<9.6f} {tail_count:<6d} {n:<5d} {p:<10d} {m}"
        )
    if rows:
        print("\nsummary")
        print(f"worst={rows[0][0]:.8f} slack={args.target_c-rows[0][0]:.8f}")
        print(f"passes={rows[0][0] <= args.target_c}")


if __name__ == "__main__":
    main()
