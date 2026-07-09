#!/usr/bin/env python3
"""#466 R269: local geometry of n=128 near-doubling joins.

R268 showed that the moderate-ancestor branch is better described by
fine128 / X64best close to 1 than by a crude X128/X64 ratio.  This probe looks
inside the top-level join eta128 = a + b and measures whether high fineRatio is
equivalent to same-phase, balanced children.
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
class JoinRow:
    p: int
    m128: int
    index128: int
    mass128: float
    x128: float
    fine128: float
    x64a: float
    x64b: float
    x64best: float
    fine64best: float
    mgf128: float
    mgf64: float
    phase_cos: float
    balance: float
    fine_ratio: float
    ratio: float


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


def rows_for_m(m128: int, chunk: int, top: int, min_fine128: float) -> list[JoinRow]:
    p = 128 * m128 + 1
    if not is_prime(p):
        return []
    eta32 = raw_periods(p, 32, chunk)
    eta64 = raw_periods(p, 64, chunk)
    eta128 = raw_periods(p, 128, chunk)
    x32 = normalized(eta32, p, 32)
    x64 = normalized(eta64, p, 64)
    x128 = normalized(eta128, p, 128)
    fine64 = x64 - np.array([x32[j % len(x32)] for j in range(len(x64))], dtype=float)
    fine128 = x128 - np.array([x64[j % len(x64)] for j in range(len(x128))], dtype=float)
    mgf128 = float(np.exp(x128 / 4.0).mean())
    mgf64 = float(np.exp(x64 / 4.0).mean())
    order = np.argsort(fine128)[::-1]
    rows: list[JoinRow] = []
    m64 = len(x64)
    for j128 in order[:top]:
        if fine128[j128] < min_fine128:
            break
        j64a = int(j128 % m64)
        j64b = int((j128 + m128) % m64)
        x64a = float(x64[j64a])
        x64b = float(x64[j64b])
        if x64a >= x64b:
            best = x64a
            fine64best = float(fine64[j64a])
        else:
            best = x64b
            fine64best = float(fine64[j64b])
        balance = min(x64a, x64b) / max(max(x64a, x64b), 1.0e-12)
        rows.append(
            JoinRow(
                p=p,
                m128=m128,
                index128=int(j128),
                mass128=math.exp(float(x128[j128]) / 4.0) / m128,
                x128=float(x128[j128]),
                fine128=float(fine128[j128]),
                x64a=x64a,
                x64b=x64b,
                x64best=best,
                fine64best=fine64best,
                mgf128=mgf128,
                mgf64=mgf64,
                phase_cos=phase_cos(eta64[j64a], eta64[j64b]),
                balance=balance,
                fine_ratio=float(fine128[j128]) / max(best, 1.0e-12),
                ratio=float(x128[j128]) / max(best, 1.0e-12),
            )
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=6000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine128", type=float, default=10.0)
    parser.add_argument("--ancestor-fine-cut", type=float, default=8.0)
    parser.add_argument("--ancestor-x-cut", type=float, default=16.0)
    parser.add_argument("--fine-ratio-cut", type=float, default=0.75)
    parser.add_argument("--balance-cuts", type=float, nargs="+", default=[0.25, 0.4, 0.6, 0.8])
    parser.add_argument("--phase-cuts", type=float, nargs="+", default=[0.9, 0.95, 0.99, 0.999])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    moderate = [
        row
        for row in rows
        if row.fine64best < args.ancestor_fine_cut and row.x64best < args.ancestor_x_cut
    ]
    near = [row for row in moderate if row.fine_ratio >= args.fine_ratio_cut]
    near.sort(key=lambda row: row.mass128, reverse=True)

    print(
        f"R269 n=128 near-doubling geometry rows={len(rows)} moderate={len(moderate)} "
        f"near={len(near)} M=[{args.min_index},{args.max_index}] fine_ratio_cut={args.fine_ratio_cut}"
    )
    print(
        f"mass moderate={sum(r.mass128 for r in moderate):.8f} "
        f"near={sum(r.mass128 for r in near):.8f}"
    )
    if near:
        balances = np.array([row.balance for row in near])
        phases = np.array([row.phase_cos for row in near])
        print(
            f"near balance median={np.median(balances):.6f} min={balances.min():.6f} "
            f"phase median={np.median(phases):.9f} min={phases.min():.9f}"
        )

    print("\ncoverage on near branch")
    print("condition       threshold count mass      worstMass worstM worstP")
    print("-" * 88)
    for cut in args.balance_cuts:
        cap = [row for row in near if row.balance >= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"balance>=      {cut:<9.3f} {len(cap):<5d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )
    for cut in args.phase_cuts:
        cap = [row for row in near if row.phase_cos >= cut]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"phase>=        {cut:<9.3f} {len(cap):<5d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )

    print("\nworst near rows")
    print("mass      X128   F128   A64    B64    bal    phase      fRatio ratio  F64best M      p       idx")
    print("-" * 122)
    for row in near[: args.top]:
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.fine128:<6.2f} {row.x64a:<6.2f} "
            f"{row.x64b:<6.2f} {row.balance:<6.3f} {row.phase_cos:<10.7f} "
            f"{row.fine_ratio:<6.3f} {row.ratio:<6.3f} {row.fine64best:<7.2f} "
            f"{row.m128:<6d} {row.p:<7d} {row.index128}"
        )


if __name__ == "__main__":
    main()
