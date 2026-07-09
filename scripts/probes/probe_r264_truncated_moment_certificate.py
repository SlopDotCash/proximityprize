#!/usr/bin/env python3
"""#466 R264: truncated/hinge moment certificates for the micro-band cap.

R243 refuted ordinary low moments as a route to S(0.75).  This probe tests a
more threshold-aware family: hinge moments around theta,

    E[(X-theta)_+^k], E[(theta-X)_+^k],

and simple Markov/Cantelli-style certificates that might bound
P[X >= theta] more tightly than raw moments.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=8)
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=16)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        s = int(np.count_nonzero(residual >= args.theta)) / case.m
        micro = s * math.exp(0.755 / 2.0)
        pos = np.maximum(residual - args.theta, 0.0)
        neg = np.maximum(args.theta - residual, 0.0)
        p1 = float(np.mean(pos))
        n1 = float(np.mean(neg))
        p2 = float(np.mean(pos * pos))
        n2 = float(np.mean(neg * neg))
        p3 = float(np.mean(pos**3))
        n3 = float(np.mean(neg**3))
        # Exact identities: mean-theta = p1-n1.  Ratios below are candidate
        # shape constraints; they are not certificates by themselves.
        rows.append(
            (
                micro,
                s,
                p1,
                n1,
                p1 / n1 if n1 else float("inf"),
                p2,
                n2,
                p2 / p1 if p1 else 0.0,
                n2 / n1 if n1 else 0.0,
                p3 / p2 if p2 else 0.0,
                n3 / n2 if n2 else 0.0,
                float(np.mean(residual)),
                case.n,
                case.p,
                case.m,
            )
        )

    rows.sort(reverse=True)
    print(f"R264 truncated moment certificate cases={len(rows)} trim={args.trim} theta={args.theta}")
    print("micro    S        p1       n1       p1/n1   p2/p1   n2/n1   p3/p2   n3/n2   mean     n     p          M")
    print("-" * 138)
    for row in rows[: args.top]:
        micro, s, p1, n1, r1, _p2, _n2, rp2, rn2, rp3, rn3, mean, n, p, m = row
        print(
            f"{micro:<8.6f} {s:<8.6f} {p1:<8.5f} {n1:<8.5f} {r1:<8.4f} "
            f"{rp2:<8.4f} {rn2:<8.4f} {rp3:<8.4f} {rn3:<8.4f} "
            f"{mean:<8.5f} {n:<5d} {p:<10d} {m}"
        )

    names = [
        "S",
        "p1",
        "n1",
        "p1/n1",
        "p2",
        "n2",
        "p2/p1",
        "n2/n1",
        "p3/p2",
        "n3/n2",
        "mean",
        "M/n",
        "logM",
    ]
    matrix = []
    target = []
    for row in rows:
        target.append(row[0])
        m = row[-1]
        n = row[-3]
        matrix.append([row[1], *row[2:12], m / n, math.log(m)])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)
    print("\ncorrelations with micro")
    scored = []
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])
        scored.append((abs(corr), name, corr))
    for _abs, name, corr in sorted(scored, reverse=True):
        print(f"{name:<8s} {corr:+.6f}")

    print("\nmax ratios")
    for idx, name in [(4, "p1/n1"), (7, "p2/p1"), (8, "n2/n1"), (9, "p3/p2")]:
        row = max(rows, key=lambda r: r[idx])
        print(
            f"{name}={row[idx]:.8f} micro={row[0]:.8f} S={row[1]:.8f} "
            f"n={row[-3]} p={row[-2]} M={row[-1]}"
        )


if __name__ == "__main__":
    main()
