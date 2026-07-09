#!/usr/bin/env python3
r"""#466 R244: Fourier structure of first-band threshold sets.

R242/R243 say the live residual cap is not a low-moment statement about the
sorted values.  This probe recomputes the unsorted quotient spectrum for the
worst rows and studies

    T = {coset index j : X_j >= theta} \ top_five

as a subset of the cyclic quotient group Z/MZ.
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


DEFAULT_CASES = [(512, 760321), (512, 620033), (512, 417793), (256, 202753)]


def parse_case(text: str) -> tuple[int, int]:
    n_text, p_text = text.split(",", 1)
    return int(n_text), int(p_text)


def max_cyclic_window_density(mask: np.ndarray, width: int) -> float:
    if width <= 0:
        return 0.0
    m = len(mask)
    width = min(width, m)
    doubled = np.concatenate([mask.astype(np.int64), mask.astype(np.int64)])
    prefix = np.concatenate([[0], np.cumsum(doubled)])
    best = int(np.max(prefix[width : width + m] - prefix[:m]))
    return best / width


def additive_energy(mask: np.ndarray) -> float:
    vals = mask.astype(np.float64)
    fft = np.fft.fft(vals)
    energy = float(np.sum(np.abs(fft) ** 4) / len(vals))
    size = float(mask.sum())
    return energy / (size**3) if size else 0.0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", type=parse_case, nargs="*", default=DEFAULT_CASES)
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--top-coeffs", type=int, default=8)
    parser.add_argument("--windows", type=int, nargs="+", default=[16, 32, 64, 128, 256])
    args = parser.parse_args()

    print(f"R244 first-band Fourier structure trim={args.trim} theta={args.theta}")
    print(
        "n     p          M      |T|    dens     half_C   maxFour  energy   "
        + " ".join(f"win{w}" for w in args.windows)
    )
    print("-" * 128)
    for n, p in args.cases:
        m = (p - 1) // n
        xs = normalized_values_vectorized(p, n, args.chunk)
        order = np.argsort(xs)[::-1]
        top = set(int(i) for i in order[: args.trim])
        mask = (xs >= args.theta)
        for idx in top:
            mask[idx] = False
        size = int(mask.sum())
        density = size / m
        half_c = density * math.exp(args.theta / 2.0)
        centered = mask.astype(np.float64) - density
        coeffs = np.fft.fft(centered)
        mags = np.abs(coeffs) / m
        max_four = float(np.max(mags[1:])) if m > 1 else 0.0
        energy = additive_energy(mask)
        window_vals = [max_cyclic_window_density(mask, w) for w in args.windows]
        print(
            f"{n:<5d} {p:<10d} {m:<6d} {size:<6d} {density:<8.6f} {half_c:<8.6f} "
            f"{max_four:<8.6f} {energy:<8.5f} "
            + " ".join(f"{v:<7.4f}" for v in window_vals)
        )

        top_freqs = np.argsort(mags[1:])[::-1][: args.top_coeffs] + 1
        print("  top frequencies:", " ".join(f"{int(k)}:{mags[k]:.5f}" for k in top_freqs))
        top_indices = sorted(top)
        print("  top deleted indices:", " ".join(str(i) for i in top_indices))


if __name__ == "__main__":
    main()
