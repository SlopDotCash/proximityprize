#!/usr/bin/env python3
"""#466 R272: moment bounds for the large-index micro-band branch.

R268 reduces the large branch to the soft target

    M >= 1536 => S(0.75) <= 0.4055.

R272 checks whether variance/centered-moment inequalities are now strong
enough, unlike in the knife-edge finite branch.
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
    parser.add_argument("--min-index", type=int, default=1536)
    parser.add_argument("--max-index", type=int, default=8000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--target-s", type=float, default=0.4055)
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
            mean = float(np.mean(residual))
            var = float(np.mean((residual - mean) ** 2))
            centered4 = float(np.mean((residual - mean) ** 4))
            second = float(np.mean(residual**2))
            # Markov on second moment: P[X>=theta] <= E[X^2]/theta^2.
            markov2 = second / (args.theta**2)
            # Cantelli upper tail bound if theta > mean; otherwise vacuous.
            if args.theta > mean:
                cantelli = var / (var + (args.theta - mean) ** 2)
            else:
                cantelli = 1.0
            rows.append((s, mean, var, centered4, second, markov2, cantelli, n, p, m))

    rows.sort(reverse=True)
    print(
        f"R272 large-index moment bounds cases={len(rows)} skipped={skipped} "
        f"targetS={args.target_s}"
    )
    print("S        slack    mean     var      c4       second   Markov2  Cantelli n     p          M")
    print("-" * 128)
    for row in rows[: args.top]:
        s, mean, var, c4, second, markov2, cantelli, n, p, m = row
        print(
            f"{s:<8.6f} {args.target_s-s:<8.6f} {mean:<8.5f} {var:<8.5f} "
            f"{c4:<8.3f} {second:<8.5f} {markov2:<8.3f} {cantelli:<8.3f} "
            f"{n:<5d} {p:<10d} {m}"
        )

    print("\nsummary")
    vals = np.array([[r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[9] / r[7], math.log(r[9])] for r in rows])
    names = ["S", "mean", "var", "centered4", "second", "Markov2", "Cantelli", "M/n", "logM"]
    for idx, name in enumerate(names):
        col = vals[:, idx]
        print(
            f"{name:<10s} median={float(np.median(col)):.6f} "
            f"p95={float(np.quantile(col,0.95)):.6f} max={float(np.max(col)):.6f}"
        )
    print("\ncorrelations with S")
    target = vals[:, 0]
    for idx, name in enumerate(names[1:], start=1):
        print(f"{name:<10s} {float(np.corrcoef(target, vals[:, idx])[0,1]):+.6f}")


if __name__ == "__main__":
    main()
