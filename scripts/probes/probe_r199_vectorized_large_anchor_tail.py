#!/usr/bin/env python3
"""#466 R199: vectorized exact stress for large dyadic tail anchors.

R198's scalar exact engine is too slow on multi-million-coset rows.  This
probe keeps the same exact coset-period computation but evaluates coset
representatives in NumPy chunks:

    eta_b = sum_{h in H} exp(2 pi i b h / p).

It is designed for a small number of hard anchors, not broad sweeps.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    primitive_root,
    subgroup,
)


ANCHORS: tuple[tuple[int, int, str], ...] = (
    (128, 268437889, "r63-control"),
    (128, 268438913, "grid-start=268435456"),
    (256, 16778497, "r184-shared-prime"),
    (256, 16780289, "grid-start=16777216"),
)


def coset_reps(p: int, n: int) -> np.ndarray:
    g = primitive_root(p)
    m = (p - 1) // n
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        reps[j] = x
        x = (x * g) % p
    return reps


def normalized_values_vectorized(p: int, n: int, chunk: int) -> np.ndarray:
    h = np.array(subgroup(p, n), dtype=np.int64)
    reps = coset_reps(p, n)
    mags = np.empty(len(reps), dtype=np.float64)
    scale = 2.0 * math.pi / p
    for start in range(0, len(reps), chunk):
        b = reps[start : start + chunk]
        residues = (b[:, None] * h[None, :]) % p
        angles = residues.astype(np.float64) * scale
        real = np.cos(angles).sum(axis=1)
        imag = np.sin(angles).sum(axis=1)
        mags[start : start + len(b)] = real * real + imag * imag
    sigma2 = n * float(mags.sum()) / (p - 1)
    return mags / sigma2


def tail_stats(xs: np.ndarray, c_bulk: float, spike_budget: float, step: float) -> tuple[float, float, float, float, int]:
    max_x = float(xs.max())
    mgf4 = float(np.exp(xs / 4).mean())
    worst_excess = -1e100
    worst_theta = 0.0
    worst_count = 0
    j = 2
    while j * step <= max_x + 1e-12:
        theta = j * step
        count = int(np.count_nonzero(xs >= theta))
        bound = c_bulk * len(xs) * math.exp(-theta / 2) + spike_budget
        excess = count - bound
        if excess > worst_excess:
            worst_excess = excess
            worst_theta = theta
            worst_count = count
        j += 1
    return worst_excess, worst_theta, max_x, mgf4, worst_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--only-small", action="store_true", help="skip p > 20M smoke-test rows")
    args = parser.parse_args()

    rows = []
    for n, p, label in ANCHORS:
        if args.only_small and p > 20_000_000:
            continue
        xs = normalized_values_vectorized(p, n, args.chunk)
        excess, theta, max_x, mgf4, count = tail_stats(xs, args.c_bulk, args.spike_budget, args.step)
        rows.append((excess, mgf4, max_x, len(xs), n, p, theta, count, label))

    rows.sort(reverse=True)
    print(f"R199 vectorized large-anchor tail stress chunk={args.chunk} tested={len(rows)}")
    print("excess    mgf1/4  maxX    M        n     p          T,count  label")
    print("-" * 96)
    for excess, mgf4, max_x, m, n, p, theta, count, label in rows:
        print(
            f"{excess:<9.3f} {mgf4:<7.4f} {max_x:<7.3f} {m:<8d} "
            f"{n:<5d} {p:<10d} {theta:<4.1f},{count:<5d} {label}"
        )
    print("\nsummary")
    print(f"max_positive_excess={max([r[0] for r in rows if r[0] > 0], default=0.0):.6f}")


if __name__ == "__main__":
    main()
