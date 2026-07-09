#!/usr/bin/env python3
"""#466 R255: geometry of top n=64 quotient representatives.

R254 shows scalar features of M do not classify the n=64 resonance family.
This probe looks at the top quotient representatives themselves: normalized
log-coordinate u=idx/M, signed representative size rep/p, gaps among top
indices on the quotient cycle, and inverse-distance pairing.  The goal is to
test for a low-dimensional phase-alignment signature before building a heavier
cyclotomic decomposition.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r199_vectorized_large_anchor_tail import coset_reps  # noqa: E402
from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    normalized_values_vectorized,
)
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import primitive_root  # noqa: E402


DEFAULT_ROWS: tuple[tuple[int, str], ...] = (
    (65537, "fermat-m1024"),
    (204353, "mgf-fail-m3193"),
    (697601, "large-index-top-m10900"),
    (665857, "large-index-square-m10404"),
    (421313, "r252-topcap-m6583"),
    (400321, "r252-residual-m6255"),
    (296833, "old-budget-m4638"),
    (355009, "moderate-control-m5547"),
)


def circular_gap(a: int, b: int, m: int) -> int:
    d = abs(a - b) % m
    return min(d, m - d)


def row_geometry(p: int, label: str, top: int, chunk: int) -> None:
    n = 64
    m = (p - 1) // n
    xs = normalized_values_vectorized(p, n, chunk)
    reps = coset_reps(p, n)
    order = [int(i) for i in np.argsort(xs)[::-1][:top]]
    g = primitive_root(p)
    top_set = set(order)

    print(f"\nrow label={label} n=64 p={p} M={m} primitive_root={g}")
    print("rank idx    u=idx/M   value     rep/p     signed/p  inv_idx inv_gap nearest_gap")
    print("-" * 96)
    sorted_idx = sorted(order)
    for rank, idx in enumerate(order, start=1):
        rep = int(reps[idx])
        inv = pow(rep, p - 2, p)
        # rep = g^idx modulo the quotient coordinate, so inversion is -idx mod M.
        inv_idx = (-idx) % m
        inv_gap = 0 if inv_idx in top_set else min(circular_gap(inv_idx, j, m) for j in top_set)
        nearest_gap = min(circular_gap(idx, j, m) for j in top_set if j != idx) if len(top_set) > 1 else 0
        signed = min(rep, p - rep)
        print(
            f"{rank:<4d} {idx:<6d} {idx / m:<9.6f} {float(xs[idx]):<9.3f} "
            f"{rep / p:<9.6f} {signed / p:<9.6f} {inv_idx:<7d} "
            f"{inv_gap:<7d} {nearest_gap}"
        )

    cyclic_gaps = []
    for a, b in zip(sorted_idx, sorted_idx[1:] + [sorted_idx[0] + m]):
        cyclic_gaps.append(b - a)
    print("top_idx_sorted", " ".join(str(x) for x in sorted_idx))
    print("cycle_gaps    ", " ".join(str(x) for x in cyclic_gaps))
    print(
        f"gap_summary min={min(cyclic_gaps)} max={max(cyclic_gaps)} "
        f"mean={sum(cyclic_gaps)/len(cyclic_gaps):.2f}"
    )
    print(f"mgf1/4={float(np.exp(xs / 4).mean()):.6f} top_mass={float(np.exp(xs[order] / 4).sum() / m):.6f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=16)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument(
        "--row",
        action="append",
        default=[],
        help="row as p,label; may be repeated. Defaults to selected n=64 rows.",
    )
    args = parser.parse_args()

    rows = []
    for row in args.row:
        p_s, label = row.split(",", 1)
        rows.append((int(p_s), label))
    if not rows:
        rows = list(DEFAULT_ROWS)

    for p, label in rows:
        row_geometry(p, label, args.top, args.chunk)


if __name__ == "__main__":
    main()
