#!/usr/bin/env python3
"""#466 R266: first n=128 check for persistent coherent path tax.

R265 left a plausible n=64 socket: after filtering exact-MGF offender rows,
persistent coherent dyadic paths carry modest positive MGF mass.  This probe
tests whether the same idea scales one level up, using the fine layer

    R = X128 - lift(X64)

and tracing the larger-child ancestry 8 -> 16 -> 32 -> 64 -> 128.
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


LEVELS = (8, 16, 32, 64, 128)


@dataclass(frozen=True)
class PathRow128:
    p: int
    m128: int
    index128: int
    fine128: float
    x128: float
    x64a: float
    x64b: float
    cos128: float
    best64: float
    best32: float
    best16: float
    best8: float
    cos64: float
    cos32: float
    cos16: float
    min_path_cos: float
    exact_mgf128: float


@dataclass(frozen=True)
class TaxRow128:
    p: int
    m: int
    exact_mgf: float
    max_fine: float
    captured: int
    captured_mass: float
    captured_scaled: float
    threshold8: float
    threshold16: float
    threshold32: float
    threshold64: float


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


def descend_best(index: int, child_n: int, etas: dict[int, np.ndarray], xs: dict[int, np.ndarray]) -> tuple[int, float, float]:
    child_m = len(xs[child_n])
    half = child_m // 2
    a = index % child_m
    b = (index + half) % child_m
    cos = phase_cos(etas[child_n][a], etas[child_n][b])
    return (a, float(xs[child_n][a]), cos) if xs[child_n][a] >= xs[child_n][b] else (b, float(xs[child_n][b]), cos)


def rows_for_m(m128: int, chunk: int, top: int, min_fine: float) -> list[PathRow128]:
    p = 128 * m128 + 1
    if not is_prime(p):
        return []
    etas = {n: raw_periods(p, n, chunk) for n in LEVELS}
    xs = {n: normalized(etas[n], p, n) for n in LEVELS}
    x128 = xs[128]
    x64 = xs[64]
    lifted64 = np.array([x64[j % len(x64)] for j in range(len(x128))], dtype=float)
    fine = x128 - lifted64
    exact_mgf128 = float(np.exp(x128 / 4.0).mean())
    order = np.argsort(fine)[::-1]
    rows: list[PathRow128] = []
    m64 = len(x64)
    for j128 in order[:top]:
        if fine[j128] < min_fine:
            break
        j64a = int(j128 % m64)
        j64b = int((j128 + m128) % m64)
        cos128 = phase_cos(etas[64][j64a], etas[64][j64b])
        if xs[64][j64a] >= xs[64][j64b]:
            j64best = j64a
            best64 = float(xs[64][j64a])
        else:
            j64best = j64b
            best64 = float(xs[64][j64b])
        j32best, best32, cos64 = descend_best(j64best, 32, etas, xs)
        j16best, best16, cos32 = descend_best(j32best, 16, etas, xs)
        _j8best, best8, cos16 = descend_best(j16best, 8, etas, xs)
        min_path_cos = min(cos128, cos64, cos32, cos16)
        rows.append(
            PathRow128(
                p=p,
                m128=m128,
                index128=int(j128),
                fine128=float(fine[j128]),
                x128=float(x128[j128]),
                x64a=float(xs[64][j64a]),
                x64b=float(xs[64][j64b]),
                cos128=cos128,
                best64=best64,
                best32=best32,
                best16=best16,
                best8=best8,
                cos64=cos64,
                cos32=cos32,
                cos16=cos16,
                min_path_cos=min_path_cos,
                exact_mgf128=exact_mgf128,
            )
        )
    return rows


def tax_for_m(
    m: int,
    rows: list[PathRow128],
    cos_floor: float,
    t8: float,
    t16: float,
    t32: float,
    t64: float,
) -> TaxRow128:
    captured = [
        row
        for row in rows
        if row.min_path_cos >= cos_floor
        and row.best8 >= t8
        and row.best16 >= t16
        and row.best32 >= t32
        and row.best64 >= t64
    ]
    captured_mass = sum(math.exp(row.x128 / 4.0) / m for row in captured)
    return TaxRow128(
        p=rows[0].p,
        m=m,
        exact_mgf=rows[0].exact_mgf128,
        max_fine=max(row.fine128 for row in rows),
        captured=len(captured),
        captured_mass=captured_mass,
        captured_scaled=captured_mass * m,
        threshold8=t8,
        threshold16=t16,
        threshold32=t32,
        threshold64=t64,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=4000)
    parser.add_argument("--chunk", type=int, default=4096)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine", type=float, default=10.0)
    parser.add_argument("--cos-floor", type=float, default=0.9)
    parser.add_argument("--max-exact-mgf", type=float, default=None)
    parser.add_argument("--t8", type=float, nargs="+", default=[5.0, 6.0, 7.0])
    parser.add_argument("--t16", type=float, nargs="+", default=[9.0, 11.0])
    parser.add_argument("--t32", type=float, nargs="+", default=[14.0, 16.0])
    parser.add_argument("--t64", type=float, nargs="+", default=[18.0, 20.0])
    parser.add_argument("--top", type=int, default=25)
    args = parser.parse_args()

    rows_by_m_raw = {
        m: rows
        for m in range(args.min_index, args.max_index + 1)
        if (rows := rows_for_m(m, args.chunk, args.top_per_row, args.min_fine))
    }
    rows_by_m = {
        m: rows
        for m, rows in rows_by_m_raw.items()
        if args.max_exact_mgf is None or rows[0].exact_mgf128 <= args.max_exact_mgf
    }
    print(
        f"R266 n=128 persistent path tax cached_rows={len(rows_by_m)} "
        f"filtered_from={len(rows_by_m_raw)} M=[{args.min_index},{args.max_index}] "
        f"min_fine={args.min_fine} top_per_row={args.top_per_row} "
        f"cos_floor={args.cos_floor} max_exact_mgf={args.max_exact_mgf}"
    )
    if rows_by_m:
        all_rows = [row for rows in rows_by_m.values() for row in rows]
        mincos = np.array([row.min_path_cos for row in all_rows])
        print(
            f"path summary rows={len(all_rows)} maxFine={max(row.fine128 for row in all_rows):.8f} "
            f"allJoinsGe={int(np.sum(mincos >= args.cos_floor))}/{len(all_rows)} "
            f"medianMinCos={float(np.median(mincos)):.8f} minMinCos={float(mincos.min()):.8f}"
        )

    candidates: list[tuple[float, TaxRow128]] = []
    for t8 in args.t8:
        for t16 in args.t16:
            for t32 in args.t32:
                for t64 in args.t64:
                    rows = [
                        tax_for_m(m, path_rows, args.cos_floor, t8, t16, t32, t64)
                        for m, path_rows in rows_by_m.items()
                    ]
                    if not rows:
                        continue
                    worst = max(rows, key=lambda row: row.captured_mass)
                    candidates.append((worst.captured_mass, worst))
                    print(
                        f"thresholds t8={t8:.1f} t16={t16:.1f} t32={t32:.1f} t64={t64:.1f} "
                        f"captured={sum(row.captured for row in rows)} "
                        f"worstMass={worst.captured_mass:.8f} worstScaled={worst.captured_scaled:.4f} "
                        f"worstM={worst.m} maxExactMGF={max(row.exact_mgf for row in rows):.4f}"
                    )

    candidates.sort(key=lambda pair: pair[0], reverse=True)
    print("\nR266 n=128 persistent path tax worst captured rows")
    print("mass      scaled  cap maxFine mgf     t8   t16  t32  t64  M      p")
    print("-" * 104)
    for _, row in candidates[: args.top]:
        print(
            f"{row.captured_mass:<9.6f} {row.captured_scaled:<7.3f} {row.captured:<3d} "
            f"{row.max_fine:<7.3f} {row.exact_mgf:<7.4f} {row.threshold8:<4.1f} "
            f"{row.threshold16:<4.1f} {row.threshold32:<4.1f} {row.threshold64:<4.1f} "
            f"{row.m:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
