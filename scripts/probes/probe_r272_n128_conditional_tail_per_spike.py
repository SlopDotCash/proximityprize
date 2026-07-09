#!/usr/bin/env python3
"""#466 R272: conditional aligned tail per top n=64 spike.

R271 suggests that n=128 near-doubling mass is top-child plus aligned tail.
This probe fixes each top-k n=64 child and scans its opposite-half partner in
the n=128 join, measuring the tail value and the induced n=128 contribution.

It reports a theorem-shaped quantity:

    max over top-k children of sum exp(X128/4)/M128
    over aligned partners satisfying tailX >= tau and fineRatio >= alpha.
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
    primitive_root,
    subgroup,
)


@dataclass(frozen=True)
class TopTailBase:
    p: int
    m128: int
    top_index: int
    top_rank: int
    top_x64: float
    partner_rank: int
    tail_x: float
    fine_ratio: float
    cos: float
    mass_if_hit: float
    mgf128: float
    mgf64: float


@dataclass(frozen=True)
class TopTailRow:
    p: int
    m128: int
    top_rank: int
    top_x64: float
    tau: float
    alpha: float
    mass: float
    partner_rank: int
    tail_x: float
    fine_ratio: float
    mgf128: float
    mgf64: float


def raw_periods(p: int, n: int, chunk: int) -> np.ndarray:
    h = subgroup(p, n)
    g = primitive_root(p)
    m = (p - 1) // n
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        reps[j] = x
        x = (x * g) % p
    out = np.empty(m, dtype=np.complex128)
    scale = 2.0 * math.pi / p
    for start in range(0, m, chunk):
        b = reps[start : start + chunk]
        residues = (b[:, None] * h[None, :]) % p
        angles = residues.astype(np.float64) * scale
        out[start : start + len(b)] = np.cos(angles).sum(axis=1) + 1j * np.sin(angles).sum(axis=1)
    return out


def normalized(eta: np.ndarray, p: int, n: int) -> np.ndarray:
    mags = np.abs(eta) ** 2
    sigma2 = n * float(mags.sum()) / (p - 1)
    return mags / sigma2


def phase_cos(a: complex, b: complex) -> float:
    denom = abs(a) * abs(b)
    return float(np.real(a * np.conj(b)) / denom) if denom else 0.0


def rows_for_m(m128: int, chunk: int, top_k: int) -> list[TopTailBase]:
    p = 128 * m128 + 1
    if not is_prime(p):
        return []
    eta64 = raw_periods(p, 64, chunk)
    eta128 = raw_periods(p, 128, chunk)
    x64 = normalized(eta64, p, 64)
    x128 = normalized(eta128, p, 128)
    mgf128 = float(np.exp(x128 / 4.0).mean())
    mgf64 = float(np.exp(x64 / 4.0).mean())
    order = np.argsort(x64)[::-1]
    ranks = np.empty(len(x64), dtype=np.int64)
    for rank, idx in enumerate(order, start=1):
        ranks[idx] = rank

    out: list[TopTailBase] = []
    for rank, top_idx in enumerate(order[:top_k], start=1):
        partner_idx = (int(top_idx) + m128) % len(x64)
        # There is exactly one opposite-half partner at this dyadic level.
        tail_x = float(x64[partner_idx])
        x_top = float(x64[top_idx])
        # Parent index is top_idx modulo M128.
        j128 = int(top_idx % m128)
        fine = float(x128[j128] - x64[j128 % len(x64)])
        fine_ratio = fine / max(x_top, 1.0e-12)
        cos = phase_cos(eta64[top_idx], eta64[partner_idx])
        mass = math.exp(float(x128[j128]) / 4.0) / m128
        out.append(
            TopTailBase(
                p=p,
                m128=m128,
                top_index=int(top_idx),
                top_rank=rank,
                top_x64=x_top,
                partner_rank=int(ranks[partner_idx]),
                tail_x=tail_x,
                fine_ratio=fine_ratio,
                cos=cos,
                mass_if_hit=mass,
                mgf128=mgf128,
                mgf64=mgf64,
            )
        )
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-k", type=int, default=8)
    parser.add_argument("--cos-floor", type=float, default=0.999)
    parser.add_argument("--taus", type=float, nargs="+", default=[2.0, 4.0, 6.0, 8.0])
    parser.add_argument("--alphas", type=float, nargs="+", default=[0.75, 0.85, 0.9, 0.95])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    summaries: list[TopTailRow] = []
    print(
        f"R272 n=128 conditional tail per spike M=[{args.min_index},{args.max_index}] "
        f"top_k={args.top_k} cos_floor={args.cos_floor}"
    )
    base_rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rows_for_m(m, args.chunk, args.top_k)
    ]
    print(f"cached_top_rows={len(base_rows)}")
    print("tau  alpha rows hits totalMass worstMass worstM worstP rank tailRank tailX fineRatio")
    print("-" * 112)
    for tau in args.taus:
        for alpha in args.alphas:
            rows = [
                TopTailRow(
                    p=row.p,
                    m128=row.m128,
                    top_rank=row.top_rank,
                    top_x64=row.top_x64,
                    tau=tau,
                    alpha=alpha,
                    mass=row.mass_if_hit,
                    partner_rank=row.partner_rank,
                    tail_x=row.tail_x,
                    fine_ratio=row.fine_ratio,
                    mgf128=row.mgf128,
                    mgf64=row.mgf64,
                )
                for row in base_rows
                if row.tail_x >= tau and row.fine_ratio >= alpha and row.cos >= args.cos_floor
            ]
            worst = max(rows, key=lambda row: row.mass) if rows else None
            if worst:
                summaries.append(worst)
            print(
                f"{tau:<4.1f} {alpha:<5.2f} {len(base_rows):<4d} {len(rows):<4d} "
                f"{sum(r.mass for r in rows):<9.6f} {(worst.mass if worst else 0):<9.6f} "
                f"{(worst.m128 if worst else 0):<6d} {(worst.p if worst else 0):<7d} "
                f"{(worst.top_rank if worst else 0):<4d} {(worst.partner_rank if worst else 0):<8d} "
                f"{(worst.tail_x if worst else 0):<5.2f} {(worst.fine_ratio if worst else 0):.3f}"
            )

    summaries.sort(key=lambda row: row.mass, reverse=True)
    print("\nworst top-tail certificates")
    print("mass      tau alpha rank topX   tailR tailX  fineRatio mgf128 mgf64  M      p")
    print("-" * 104)
    for row in summaries[: args.top]:
        print(
            f"{row.mass:<9.6f} {row.tau:<3.1f} {row.alpha:<5.2f} {row.top_rank:<4d} "
            f"{row.top_x64:<6.2f} {row.partner_rank:<5d} {row.tail_x:<6.2f} "
            f"{row.fine_ratio:<9.3f} {row.mgf128:<6.3f} {row.mgf64:<6.3f} "
            f"{row.m128:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
