#!/usr/bin/env python3
"""#466 R264: multilevel ancestry of n=64 child-coherence spikes.

R263 found that dangerous n=64 fine residuals are two-child phase-coherence
events in eta64[j] = eta32[j] + eta32[j + M].  This probe checks a stronger
possible repair hypothesis: do those spikes come from persistent coherent
choices down the dyadic tower 8 -> 16 -> 32 -> 64?

For each high fine spike at n=64 it traces both n=32 children, each n=32 child
back to its two n=16 children, and each selected n=16 child back to n=8.  The
reported path chooses the larger-magnitude child at every descent.
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
class PathRow:
    p: int
    m64: int
    index64: int
    fine64: float
    x64: float
    x32a: float
    x32b: float
    cos64: float
    best32: float
    best16: float
    best8: float
    cos32: float
    cos16: float
    min_path_cos: float
    path_gain: float
    exact_mgf64: float


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


def best_child(index: int, parent_n: int, child_x: np.ndarray) -> tuple[int, float]:
    """For parent order 2n at index j, return larger child at order n."""
    child_m = len(child_x)
    half = child_m // 2
    a = index % child_m
    b = (index + half) % child_m
    return (a, float(child_x[a])) if child_x[a] >= child_x[b] else (b, float(child_x[b]))


def rows_for_m(m64: int, chunk: int, top: int, min_fine: float) -> list[PathRow]:
    p = 64 * m64 + 1
    if not is_prime(p):
        return []
    etas = {n: raw_periods(p, n, chunk) for n in (8, 16, 32, 64)}
    xs = {n: normalized(etas[n], p, n) for n in (8, 16, 32, 64)}
    x64 = xs[64]
    x32 = xs[32]
    lifted32 = np.array([x32[j % len(x32)] for j in range(len(x64))], dtype=float)
    fine = x64 - lifted32
    exact_mgf64 = float(np.exp(x64 / 4.0).mean())
    order = np.argsort(fine)[::-1]
    rows: list[PathRow] = []
    m32 = len(x32)
    for j64 in order[:top]:
        if fine[j64] < min_fine:
            break
        j32a = int(j64 % m32)
        j32b = int((j64 + m64) % m32)
        cos64 = phase_cos(etas[32][j32a], etas[32][j32b])
        if xs[32][j32a] >= xs[32][j32b]:
            j32best = j32a
            best32 = float(xs[32][j32a])
        else:
            j32best = j32b
            best32 = float(xs[32][j32b])

        m16 = len(xs[16])
        j16a = j32best % m16
        j16b = (j32best + m16 // 2) % m16
        cos32 = phase_cos(etas[16][j16a], etas[16][j16b])
        if xs[16][j16a] >= xs[16][j16b]:
            j16best = j16a
            best16 = float(xs[16][j16a])
        else:
            j16best = j16b
            best16 = float(xs[16][j16b])

        m8 = len(xs[8])
        j8a = j16best % m8
        j8b = (j16best + m8 // 2) % m8
        cos16 = phase_cos(etas[8][j8a], etas[8][j8b])
        best8 = float(max(xs[8][j8a], xs[8][j8b]))
        min_path_cos = min(cos64, cos32, cos16)
        path_gain = float(x64[j64] / max(best8, 1.0e-12))
        rows.append(
            PathRow(
                p=p,
                m64=m64,
                index64=int(j64),
                fine64=float(fine[j64]),
                x64=float(x64[j64]),
                x32a=float(xs[32][j32a]),
                x32b=float(xs[32][j32b]),
                cos64=cos64,
                best32=best32,
                best16=best16,
                best8=best8,
                cos32=cos32,
                cos16=cos16,
                min_path_cos=min_path_cos,
                path_gain=path_gain,
                exact_mgf64=exact_mgf64,
            )
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--top-per-row", type=int, default=2)
    parser.add_argument("--min-fine", type=float, default=10.0)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--sort", choices=["fine64", "x64", "min_path_cos", "path_gain"], default="fine64")
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in rows_for_m(m, args.chunk, args.top_per_row, args.min_fine)
    ]
    key = {
        "fine64": lambda row: row.fine64,
        "x64": lambda row: row.x64,
        "min_path_cos": lambda row: row.min_path_cos,
        "path_gain": lambda row: row.path_gain,
    }[args.sort]
    rows.sort(key=key, reverse=True)

    print(
        f"R264 n=64 multilevel coherence rows={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] min_fine={args.min_fine} sort={args.sort}"
    )
    print(
        "score    fine64 X64    c64    X32a   X32b   best32 best16 best8  c32    c16    minCos gain   mgf64  idx    M      p"
    )
    print("-" * 142)
    for row in rows[: args.top]:
        print(
            f"{key(row):<8.4f} {row.fine64:<6.2f} {row.x64:<6.2f} {row.cos64:<6.3f} "
            f"{row.x32a:<6.2f} {row.x32b:<6.2f} {row.best32:<6.2f} {row.best16:<6.2f} "
            f"{row.best8:<6.2f} {row.cos32:<6.3f} {row.cos16:<6.3f} {row.min_path_cos:<6.3f} "
            f"{row.path_gain:<6.2f} {row.exact_mgf64:<6.3f} {row.index64:<6d} {row.m64:<6d} {row.p}"
        )

    if rows:
        cos64 = np.array([row.cos64 for row in rows])
        cos32 = np.array([row.cos32 for row in rows])
        cos16 = np.array([row.cos16 for row in rows])
        mincos = np.array([row.min_path_cos for row in rows])
        print("\nsummary")
        print(f"max_fine64={max(row.fine64 for row in rows):.8f}")
        print(f"cos64_ge_0.9={int(np.sum(cos64 >= 0.9))}/{len(rows)}")
        print(f"cos32_ge_0.9={int(np.sum(cos32 >= 0.9))}/{len(rows)}")
        print(f"cos16_ge_0.9={int(np.sum(cos16 >= 0.9))}/{len(rows)}")
        print(f"all_three_ge_0.9={int(np.sum(mincos >= 0.9))}/{len(rows)}")
        print(f"median_min_path_cos={float(np.median(mincos)):.8f}")
        print(f"min_min_path_cos={float(mincos.min()):.8f}")


if __name__ == "__main__":
    main()
