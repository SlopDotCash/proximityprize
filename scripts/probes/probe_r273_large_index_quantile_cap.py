#!/usr/bin/env python3
"""#466 R273: quantile caps for the large-index micro-band branch."""

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
    parser.add_argument("--min-index", type=int, default=1536)
    parser.add_argument("--max-index", type=int, default=8000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--stride", type=int, default=1, help="test only indices M with (M-min-index) divisible by stride")
    parser.add_argument("--limit-per-n", type=int, default=0, help="0 means no per-n limit")
    args = parser.parse_args()

    rows = []
    for n in args.ns:
        tested_for_n = 0
        for m in range(args.min_index, args.max_index + 1):
            if (m - args.min_index) % args.stride != 0:
                continue
            p = m * n + 1
            if not is_prime(p):
                continue
            cached = cached_desc(p, n, args.chunk, args.cache_dir, args.cache_only)
            if cached is None:
                continue
            _xs, desc = cached
            residual = desc[min(args.trim, len(desc)) :]
            s = int(np.count_nonzero(residual >= args.theta)) / m
            qs = [float(np.quantile(residual, q)) for q in [0.55, 0.575, 0.6, 0.625, 0.65]]
            rows.append((s, *qs, n, p, m))
            tested_for_n += 1
            if args.limit_per_n and tested_for_n >= args.limit_per_n:
                break

    rows.sort(reverse=True)
    print(f"R273 large-index quantile cap cases={len(rows)}")
    print("S        q55      q575     q60      q625     q65      n     p          M")
    print("-" * 104)
    for row in rows[: args.top]:
        s, q55, q575, q60, q625, q65, n, p, m = row
        print(
            f"{s:<8.6f} {q55:<8.6f} {q575:<8.6f} {q60:<8.6f} "
            f"{q625:<8.6f} {q65:<8.6f} {n:<5d} {p:<10d} {m}"
        )

    print("\nquantile maxima")
    labels = ["q55", "q575", "q60", "q625", "q65"]
    for idx, label in enumerate(labels, start=1):
        row = max(rows, key=lambda r: r[idx])
        print(f"{label} max={row[idx]:.8f} S={row[0]:.8f} n={row[-3]} p={row[-2]} M={row[-1]}")

    print("\ncorrelations with S")
    vals = np.array([[r[i] for i in range(6)] + [r[-1] / r[-3], math.log(r[-1])] for r in rows])
    names = ["S", *labels, "M/n", "logM"]
    target = vals[:, 0]
    for idx, name in enumerate(names[1:], start=1):
        print(f"{name:<8s} {float(np.corrcoef(target, vals[:,idx])[0,1]):+.6f}")


if __name__ == "__main__":
    main()
