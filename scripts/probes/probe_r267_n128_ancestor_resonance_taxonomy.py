#!/usr/bin/env python3
"""#466 R267: n=128 coherent paths by n=64 ancestor resonance.

R266 showed that the simple current-level MGF filter does not make the
persistent path tax small at n=128: p=665857 has exact MGF128 < 2 but a large
coherent n=128 path descending from an already-resonant n=64 branch.

This probe labels high n=128 fine spikes by the best n=64 ancestor and asks
whether a recursive ancestor taxonomy can isolate the dangerous mass.
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
class AncestorRow:
    p: int
    m128: int
    index128: int
    index64: int
    fine128: float
    x128: float
    mass128: float
    mgf128: float
    x64: float
    fine64: float
    mgf64: float
    best32: float
    best16: float
    best8: float
    min_cos128_path: float


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


def rows_for_m(m128: int, chunk: int, top: int, min_fine128: float) -> list[AncestorRow]:
    p = 128 * m128 + 1
    if not is_prime(p):
        return []
    etas = {n: raw_periods(p, n, chunk) for n in LEVELS}
    xs = {n: normalized(etas[n], p, n) for n in LEVELS}
    fine128 = xs[128] - np.array([xs[64][j % len(xs[64])] for j in range(len(xs[128]))])
    fine64 = xs[64] - np.array([xs[32][j % len(xs[32])] for j in range(len(xs[64]))])
    mgf128 = float(np.exp(xs[128] / 4.0).mean())
    mgf64 = float(np.exp(xs[64] / 4.0).mean())
    order = np.argsort(fine128)[::-1]
    rows: list[AncestorRow] = []
    m64 = len(xs[64])
    for j128 in order[:top]:
        if fine128[j128] < min_fine128:
            break
        j64a = int(j128 % m64)
        j64b = int((j128 + m128) % m64)
        cos128 = phase_cos(etas[64][j64a], etas[64][j64b])
        if xs[64][j64a] >= xs[64][j64b]:
            j64best = j64a
            x64best = float(xs[64][j64a])
        else:
            j64best = j64b
            x64best = float(xs[64][j64b])
        j32best, best32, cos64 = descend_best(j64best, 32, etas, xs)
        j16best, best16, cos32 = descend_best(j32best, 16, etas, xs)
        _j8best, best8, cos16 = descend_best(j16best, 8, etas, xs)
        rows.append(
            AncestorRow(
                p=p,
                m128=m128,
                index128=int(j128),
                index64=j64best,
                fine128=float(fine128[j128]),
                x128=float(xs[128][j128]),
                mass128=math.exp(float(xs[128][j128]) / 4.0) / m128,
                mgf128=mgf128,
                x64=x64best,
                fine64=float(fine64[j64best]),
                mgf64=mgf64,
                best32=best32,
                best16=best16,
                best8=best8,
                min_cos128_path=min(cos128, cos64, cos32, cos16),
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
    parser.add_argument("--cos-floor", type=float, default=0.9)
    parser.add_argument("--ancestor-fine64", type=float, nargs="+", default=[8.0, 10.0, 12.0, 14.0])
    parser.add_argument("--ancestor-x64", type=float, nargs="+", default=[14.0, 16.0, 18.0, 20.0])
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rows_for_m(m, args.chunk, args.top_per_row, args.min_fine128)
    ]
    coherent = [row for row in rows if row.min_cos128_path >= args.cos_floor]
    coherent.sort(key=lambda row: row.mass128, reverse=True)
    print(
        f"R267 n=128 ancestor resonance rows={len(rows)} coherent={len(coherent)} "
        f"M=[{args.min_index},{args.max_index}] min_fine128={args.min_fine128}"
    )
    if coherent:
        print(
            f"max_mass={coherent[0].mass128:.8f} max_x128={max(r.x128 for r in coherent):.6f} "
            f"max_fine128={max(r.fine128 for r in coherent):.6f}"
        )

    print("\nancestor threshold coverage")
    print("kind threshold captured mass      worstMass worstM worstP")
    print("-" * 86)
    for t in args.ancestor_fine64:
        cap = [row for row in coherent if row.fine64 >= t]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"fine64 {t:<9.2f} {len(cap):<8d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )
    for t in args.ancestor_x64:
        cap = [row for row in coherent if row.x64 >= t]
        worst = max(cap, key=lambda row: row.mass128) if cap else None
        print(
            f"x64    {t:<9.2f} {len(cap):<8d} {sum(r.mass128 for r in cap):<9.6f} "
            f"{(worst.mass128 if worst else 0):<9.6f} {(worst.m128 if worst else 0):<6d} "
            f"{(worst.p if worst else 0)}"
        )

    print("\nworst coherent rows")
    print("mass      X128   F128   X64    F64    mgf128 mgf64  b32   b16   b8    M      p       idx128 idx64")
    print("-" * 124)
    for row in coherent[: args.top]:
        print(
            f"{row.mass128:<9.6f} {row.x128:<6.2f} {row.fine128:<6.2f} {row.x64:<6.2f} "
            f"{row.fine64:<6.2f} {row.mgf128:<6.3f} {row.mgf64:<6.3f} "
            f"{row.best32:<5.1f} {row.best16:<5.1f} {row.best8:<5.1f} "
            f"{row.m128:<6d} {row.p:<7d} {row.index128:<6d} {row.index64}"
        )


if __name__ == "__main__":
    main()
