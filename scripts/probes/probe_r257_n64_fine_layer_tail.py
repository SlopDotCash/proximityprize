#!/usr/bin/env python3
"""#466 R257: tail profile of the fine layer X_64 - lifted(X_32).

R256 found that n=64 spikes are not merely inherited from divisor spectra:
subtracting the lifted n=32 layer leaves a large positive fine residual on the
top rows.  This probe treats that fine residual as its own spectrum and measures
whether it has a cleaner top-rank/tail law than the full X_64 spectrum.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)


@dataclass(frozen=True)
class Row:
    p: int
    m: int
    full_mgf: float
    fine_mgf: float
    fine_max: float
    fine_top8: float
    fine_top16: float
    full_max: float
    full_top8: float
    c_tail: float
    theta_tail: float
    count_tail: int
    trim: int


def lift32_to64(x32: np.ndarray, m64: int) -> np.ndarray:
    m32 = len(x32)
    return np.array([x32[j % m32] for j in range(m64)], dtype=float)


def tail_constant(desc: np.ndarray, tau: float, trim: int) -> tuple[float, float, int]:
    m = len(desc)
    best = (0.0, tau, 0)
    for idx, value in enumerate(desc[min(trim, m) :], start=1):
        theta = float(value)
        if theta <= tau:
            break
        c = (idx / m) * math.exp(theta / 2.0)
        if c > best[0]:
            best = (c, theta, idx)
    return best


def row_for_m(m: int, chunk: int, tau: float, trim: int) -> Row | None:
    p = 64 * m + 1
    if not is_prime(p):
        return None
    x64 = normalized_values_vectorized(p, 64, chunk)
    x32 = normalized_values_vectorized(p, 32, chunk)
    fine = x64 - lift32_to64(x32, len(x64))
    full_desc = np.sort(x64)[::-1]
    fine_desc = np.sort(fine)[::-1]
    c_tail, theta_tail, count_tail = tail_constant(fine_desc, tau, trim)
    return Row(
        p=p,
        m=m,
        full_mgf=float(np.exp(x64 / 4.0).mean()),
        fine_mgf=float(np.exp(fine / 4.0).mean()),
        fine_max=float(fine_desc[0]),
        fine_top8=float(np.exp(fine_desc[:8] / 4.0).sum() / len(fine_desc)),
        fine_top16=float(np.exp(fine_desc[:16] / 4.0).sum() / len(fine_desc)),
        full_max=float(full_desc[0]),
        full_top8=float(np.exp(full_desc[:8] / 4.0).sum() / len(full_desc)),
        c_tail=c_tail,
        theta_tail=theta_tail,
        count_tail=count_tail,
        trim=trim,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--trim", type=int, default=0)
    parser.add_argument("--sort", choices=["fine_max", "fine_top8", "fine_mgf", "c_tail"], default="fine_top8")
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        if (row := row_for_m(m, args.chunk, args.tau, args.trim)) is not None
    ]
    rows.sort(key=lambda row: getattr(row, args.sort), reverse=True)

    print(
        f"R257 n=64 fine-layer tail cases={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] tau={args.tau} trim={args.trim} sort={args.sort}"
    )
    print(
        "score    fineTop8 fineTop16 fineMGF fineMax cTail   theta   count "
        "fullTop8 fullMGF fullMax M      p"
    )
    print("-" * 124)
    for row in rows[: args.top]:
        print(
            f"{getattr(row, args.sort):<8.4f} {row.fine_top8:<8.4f} {row.fine_top16:<9.4f} "
            f"{row.fine_mgf:<7.4f} {row.fine_max:<7.3f} {row.c_tail:<7.4f} "
            f"{row.theta_tail:<7.3f} {row.count_tail:<5d} {row.full_top8:<8.4f} "
            f"{row.full_mgf:<7.4f} {row.full_max:<7.3f} {row.m:<6d} {row.p}"
        )

    if rows:
        print("\nsummary")
        for name in ("fine_top8", "fine_top16", "fine_mgf", "fine_max", "c_tail"):
            row = max(rows, key=lambda r: getattr(r, name))
            print(
                f"max_{name}=M{row.m}_p{row.p} value={getattr(row, name):.8f} "
                f"fullTop8={row.full_top8:.8f} fullMGF={row.full_mgf:.8f}"
            )


if __name__ == "__main__":
    main()
