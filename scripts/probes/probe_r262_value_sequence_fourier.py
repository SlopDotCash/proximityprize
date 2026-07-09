#!/usr/bin/env python3
"""#466 R262: Fourier features of the quotient value sequence.

R244 showed first-band threshold sets are Fourier-uniform.  R262 instead
studies the unsorted value sequence X_j over quotient indices j, asking whether
low-mode value energy predicts the micro-band cap S(0.75).
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import normalized_values_vectorized  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def spectral_features(xs: np.ndarray, trim: int) -> tuple[float, float, float, float, float]:
    order = np.argsort(xs)[::-1]
    mask_top = np.zeros(len(xs), dtype=bool)
    mask_top[order[:trim]] = True
    residual = xs.copy()
    residual[mask_top] = float(np.mean(xs[~mask_top]))
    centered = residual - float(np.mean(residual))
    fft = np.fft.fft(centered)
    power = np.abs(fft) ** 2
    total = float(np.sum(power[1:]))
    if total <= 0:
        return (0.0, 0.0, 0.0, 0.0, 0.0)
    m = len(xs)
    low8 = float(np.sum(power[1 : min(9, m)])) / total
    low32 = float(np.sum(power[1 : min(33, m)])) / total
    max_coeff = float(np.max(np.abs(fft[1:])) / m)
    spectral_entropy = float(-np.sum((power[1:] / total) * np.log(power[1:] / total + 1.0e-300)))
    l2 = float(np.sqrt(np.mean(centered * centered)))
    return low8, low32, max_coeff, spectral_entropy, l2


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
    parser.add_argument("--top", type=int, default=20)
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
        # Cache stores desc; recompute unsorted exact sequence for Fourier features.
        xs = normalized_values_vectorized(case.p, case.n, args.chunk)
        desc = np.sort(xs)[::-1]
        residual_desc = desc[min(args.trim, len(desc)) :]
        s075 = int(np.count_nonzero(residual_desc >= args.theta)) / case.m
        micro = s075 * math.exp(0.755 / 2.0)
        low8, low32, max_coeff, entropy, l2 = spectral_features(xs, args.trim)
        rows.append((micro, s075, low8, low32, max_coeff, entropy, l2, case.n, case.p, case.m))

    rows.sort(reverse=True)
    print(f"R262 value-sequence Fourier cases={len(rows)} trim={args.trim}")
    print("micro    S075     low8     low32    maxCoef  entropy  l2       n     p          M")
    print("-" * 112)
    for row in rows[: args.top]:
        micro, s075, low8, low32, max_coeff, entropy, l2, n, p, m = row
        print(
            f"{micro:<8.6f} {s075:<8.6f} {low8:<8.5f} {low32:<8.5f} "
            f"{max_coeff:<8.5f} {entropy:<8.3f} {l2:<8.5f} {n:<5d} {p:<10d} {m}"
        )

    names = ["low8", "low32", "maxCoef", "entropy", "l2", "M/n", "logM"]
    matrix = []
    target = []
    for row in rows:
        target.append(row[0])
        m = row[-1]
        n = row[-3]
        matrix.append([*row[2:7], m / n, math.log(m)])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)
    print("\ncorrelations with micro")
    for idx, name in enumerate(names):
        print(f"{name:<8s} {float(np.corrcoef(target_np, matrix_np[:,idx])[0,1]):+.6f}")


if __name__ == "__main__":
    main()
