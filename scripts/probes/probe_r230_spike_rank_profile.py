#!/usr/bin/env python3
"""#466 R230: rank profile of spike-resonant quotient spectra.

The R229 cutoff scan showed that direct quarter-MGF failures are rare and
driven by large spikes.  This probe decomposes

    mean_q exp(X_q / 4)

by descending rank of the quotient normalized-square values `X_q`.  It reports
how much of the MGF is carried by the top 1, 2, 4, ... quotient orbits and
compares known bad rows with nearby passing rows.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    factor,
    normalized_values_vectorized,
)


DEFAULT_CASES: tuple[tuple[int, int, str], ...] = (
    (64, 7937, "bad-M124"),
    (64, 48449, "bad-M757"),
    (64, 63361, "bad-M990"),
    (64, 65537, "bad-M1024"),
    (64, 204353, "bad-M3193"),
    (128, 65537, "bad-n128-M512"),
    (64, 65921, "near-pass-M1030"),
    (64, 259201, "env-fail-mgf-pass-M4050"),
    (64, 421313, "env-fail-mgf-pass-M6583"),
    (256, 16778497, "large-anchor"),
    (64, 16778497, "large-anchor"),
)


def top_contributions(xs: np.ndarray, ranks: list[int]) -> tuple[np.ndarray, dict[int, float]]:
    weights = np.exp(xs / 4.0)
    order = np.argsort(weights)[::-1]
    sorted_weights = weights[order]
    cumulative = np.cumsum(sorted_weights) / len(xs)
    out: dict[int, float] = {}
    for rank in ranks:
        if rank <= 0:
            continue
        out[rank] = float(cumulative[min(rank, len(xs)) - 1])
    return order, out


def quantiles(xs: np.ndarray) -> tuple[float, float, float, float]:
    return tuple(float(np.quantile(xs, q)) for q in (0.5, 0.9, 0.99, 0.999))  # type: ignore[return-value]


def rank_barrier_excess(xs: np.ndarray, order: np.ndarray, m: int, ranks: list[int]) -> dict[int, float]:
    out: dict[int, float] = {}
    for rank in ranks:
        if rank <= 0 or rank > len(order):
            continue
        x = float(xs[order[rank - 1]])
        out[rank] = x - 4.0 * math.log(m / rank)
    return out


def row(n: int, p: int, label: str, chunk: int, ranks: list[int]) -> tuple:
    xs = normalized_values_vectorized(p, n, chunk)
    order, contrib = top_contributions(xs, ranks)
    barriers = rank_barrier_excess(xs, order, len(xs), ranks)
    top_x = [float(xs[i]) for i in order[: min(8, len(order))]]
    m = len(xs)
    mgf = float(np.exp(xs / 4.0).mean())
    med, q90, q99, q999 = quantiles(xs)
    return (
        mgf,
        max(top_x, default=0.0),
        contrib,
        barriers,
        top_x,
        med,
        q90,
        q99,
        q999,
        m,
        n,
        p,
        label,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--ranks", type=int, nargs="+", default=[1, 2, 4, 8, 16, 32, 64])
    parser.add_argument(
        "--case",
        action="append",
        default=[],
        help="extra case as n:p:label",
    )
    args = parser.parse_args()

    cases = list(DEFAULT_CASES)
    for spec in args.case:
        n_s, p_s, label = spec.split(":", 2)
        cases.append((int(n_s), int(p_s), label))

    rows = [row(n, p, label, args.chunk, args.ranks) for n, p, label in cases]
    rows.sort(reverse=True, key=lambda r: r[0])

    rank_header = " ".join(f"top{rank:<3d}" for rank in args.ranks)
    print(f"R230 spike-rank profile ranks={args.ranks}")
    print(
        "mgf1/4  topX    q50    q90    q99    q999   M        n     p          "
        f"{rank_header} label"
    )
    print("-" * (116 + 8 * len(args.ranks)))
    for mgf, max_x, contrib, barriers, top_x, med, q90, q99, q999, m, n, p, label in rows:
        contrib_s = " ".join(f"{contrib.get(rank, 0.0):<7.3f}" for rank in args.ranks)
        print(
            f"{mgf:<7.4f} {max_x:<7.3f} {med:<6.3f} {q90:<6.3f} {q99:<6.3f} "
            f"{q999:<6.3f} {m:<8d} {n:<5d} {p:<10d} {contrib_s} {label}"
        )
        print(
            "  topX="
            + ", ".join(f"{x:.4f}" for x in top_x)
            + f"  factors(M)={factor(m)} p_mod_256={p % 256}"
        )
        print(
            "  barrier_excess="
            + ", ".join(f"r{rank}:{barriers.get(rank, float('nan')):.3f}" for rank in args.ranks)
        )


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(130)
