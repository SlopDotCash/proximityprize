#!/usr/bin/env python3
"""#466 R232: inspect arithmetic signatures of top quotient spikes.

R231 suggests paying the top five quotient orbits exactly.  This probe inspects
the actual top coset representatives for selected exact rows and reports simple
arithmetic features: primitive-root exponent, negation/inverse partners, and
near-collisions among the top values.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r199_vectorized_large_anchor_tail import coset_reps  # noqa: E402
from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    normalized_values_vectorized,
)
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import primitive_root  # noqa: E402


DEFAULT_ROWS: tuple[tuple[int, int, str], ...] = (
    (256, 771073, "top4-refuter-fifth-spike"),
    (512, 417793, "trim5-C-witness"),
    (512, 566273, "trim5-budget-witness"),
    (512, 760321, "trim6-near-witness"),
)


def dlog_table(p: int, g: int) -> dict[int, int]:
    out: dict[int, int] = {}
    x = 1
    for j in range(p - 1):
        out[x] = j
        x = (x * g) % p
    return out


def signed_min(x: int, p: int) -> int:
    return min(x, p - x)


def inspect_row(n: int, p: int, label: str, top: int, chunk: int) -> None:
    xs = normalized_values_vectorized(p, n, chunk)
    reps = coset_reps(p, n)
    order = np.argsort(xs)[::-1][:top]
    g = primitive_root(p)
    logs = dlog_table(p, g)
    m = (p - 1) // n
    top_set = {int(i) for i in order}
    print(f"\nrow n={n} p={p} M={m} label={label} primitive_root={g}")
    print("rank idx   log_g idx? value      rep        signed     inv_idx neg_idx in_top_inv in_top_neg")
    print("-" * 108)
    for rank, idx0 in enumerate(order, start=1):
        idx = int(idx0)
        rep = int(reps[idx])
        inv = pow(rep, p - 2, p)
        neg = (-rep) % p
        inv_idx = logs[inv] % m
        neg_idx = logs[neg] % m
        print(
            f"{rank:<4d} {idx:<5d} {logs[rep]:<5d} {idx == logs[rep] % m!s:<4s} "
            f"{float(xs[idx]):<10.6f} {rep:<10d} {signed_min(rep, p):<10d} "
            f"{inv_idx:<7d} {neg_idx:<7d} {inv_idx in top_set!s:<10s} {neg_idx in top_set!s:<10s}"
        )

    vals = [float(xs[int(i)]) for i in order]
    gaps = [vals[i] - vals[i + 1] for i in range(len(vals) - 1)]
    print("top_values", " ".join(f"{v:.6f}" for v in vals))
    print("top_gaps  ", " ".join(f"{g0:.6f}" for g0 in gaps))
    print(f"mgf1/4={float(np.exp(xs / 4).mean()):.6f} maxX={float(xs.max()):.6f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument(
        "--row",
        action="append",
        default=[],
        help="row as n,p,label; may be repeated. Defaults to R231 witness rows.",
    )
    args = parser.parse_args()

    rows = []
    for row in args.row:
        parts = row.split(",", 2)
        if len(parts) != 3:
            raise ValueError("--row must be n,p,label")
        rows.append((int(parts[0]), int(parts[1]), parts[2]))
    if not rows:
        rows = list(DEFAULT_ROWS)

    for n, p, label in rows:
        inspect_row(n, p, label, args.top, args.chunk)


if __name__ == "__main__":
    main()
