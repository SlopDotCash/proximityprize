#!/usr/bin/env python3
"""#466 R256: divisor-layer correlations for n=64 resonance rows.

For p = 64M+1, compare the n=64 quotient spectrum with coarser spectra for
divisors d | 64.  Each n=64 quotient coset lies inside a d-quotient coset, so
we can ask whether large n=64 spikes are inherited from d=8/16/32 structure or
from a genuinely fine residual inside a coarse layer.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    normalized_values_vectorized,
)


DEFAULT_ROWS: tuple[tuple[int, str], ...] = (
    (697601, "large-index-top-m10900"),
    (665857, "large-index-square-m10404"),
    (204353, "mgf-fail-m3193"),
    (65537, "fermat-m1024"),
    (421313, "r252-topcap-m6583"),
    (400321, "r252-residual-m6255"),
    (355009, "moderate-control-m5547"),
)


def expand_coarse_to_n64(coarse: np.ndarray, d: int, m64: int) -> np.ndarray:
    """Map d-spectrum quotient rows onto the n=64 quotient coordinate.

    `p-1 = 64*M`.  For divisor d, the quotient carrier has size `(p-1)/d`.
    The n=64 quotient index j maps to coarse index j modulo `(p-1)/d`.
    """

    md = len(coarse)
    return np.array([coarse[j % md] for j in range(m64)], dtype=float)


def corr(a: np.ndarray, b: np.ndarray) -> float:
    a0 = a - float(a.mean())
    b0 = b - float(b.mean())
    denom = math.sqrt(float(np.dot(a0, a0)) * float(np.dot(b0, b0)))
    if denom == 0.0:
        return 0.0
    return float(np.dot(a0, b0) / denom)


def analyze_row(p: int, label: str, divisors: list[int], top: int, chunk: int) -> None:
    x64 = normalized_values_vectorized(p, 64, chunk)
    m64 = len(x64)
    top_idx = [int(i) for i in np.argsort(x64)[::-1][:top]]

    print(f"\nrow label={label} p={p} M64={m64}")
    print("divisor corr_all top_mean coarse_top_mean residual_top_mean residual_max")
    print("-" * 88)
    expanded: dict[int, np.ndarray] = {}
    for d in divisors:
        xd = normalized_values_vectorized(p, d, chunk)
        ed = expand_coarse_to_n64(xd, d, m64)
        expanded[d] = ed
        residual = x64 - ed
        print(
            f"{d:<7d} {corr(x64, ed):<8.4f} "
            f"{float(x64[top_idx].mean()):<8.3f} {float(ed[top_idx].mean()):<15.3f} "
            f"{float(residual[top_idx].mean()):<17.3f} {float(residual.max()):.3f}"
        )

    print("\ntop rows")
    header = "rank idx X64    " + " ".join(f"X{d:<5d} R{d:<5d}" for d in divisors)
    print(header)
    print("-" * len(header))
    for rank, idx in enumerate(top_idx, start=1):
        parts = [f"{rank:<4d} {idx:<5d} {float(x64[idx]):<7.3f}"]
        for d in divisors:
            coarse = expanded[d][idx]
            parts.append(f"{float(coarse):<7.3f} {float(x64[idx] - coarse):<7.3f}")
        print(" ".join(parts))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--divisors", type=int, nargs="+", default=[8, 16, 32])
    parser.add_argument("--row", action="append", default=[], help="row as p,label")
    args = parser.parse_args()

    rows = []
    for row in args.row:
        p_s, label = row.split(",", 1)
        rows.append((int(p_s), label))
    if not rows:
        rows = list(DEFAULT_ROWS)

    for p, label in rows:
        analyze_row(p, label, args.divisors, args.top, args.chunk)


if __name__ == "__main__":
    main()
