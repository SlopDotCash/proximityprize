#!/usr/bin/env python3
"""#466 R263: child-phase anatomy of n=64 fine spikes.

For p = 64*M + 1, the n=64 subgroup splits as

    mu_64 = mu_32 disjoint_union zeta * mu_32.

Thus each n=64 period is a two-child sum of n=32 periods:

    eta64[j] = eta32[j] + eta32[j + M].

R257--R262 showed that positive fine-layer tails are blocked by isolated
survivors.  This probe asks whether those survivors are simply pair-phase
alignment events in the two-child decomposition, or whether a repair must
already see higher correlations.
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
class Spike:
    p: int
    m: int
    index: int
    fine: float
    x64: float
    lift32: float
    child_a: float
    child_b: float
    phase_cos: float
    pair_score: float
    exact_mgf: float


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


def normalized_from_raw(eta: np.ndarray, p: int, n: int) -> np.ndarray:
    mags = np.abs(eta) ** 2
    sigma2 = n * float(mags.sum()) / (p - 1)
    return mags / sigma2


def spikes_for_m(m: int, chunk: int, top: int, min_fine: float) -> list[Spike]:
    p = 64 * m + 1
    if not is_prime(p):
        return []
    eta64 = raw_periods(p, 64, chunk)
    eta32 = raw_periods(p, 32, chunk)
    x64 = normalized_from_raw(eta64, p, 64)
    x32 = normalized_from_raw(eta32, p, 32)
    lifted = np.array([x32[j % (2 * m)] for j in range(m)], dtype=float)
    fine = x64 - lifted
    order = np.argsort(fine)[::-1]
    exact_mgf = float(np.exp(x64 / 4.0).mean())
    rows: list[Spike] = []
    for j in order[:top]:
        if fine[j] < min_fine:
            break
        a = eta32[j]
        b = eta32[j + m]
        na = abs(a)
        nb = abs(b)
        denom = 2.0 * na * nb
        phase_cos = float(np.real(a * np.conj(b)) / (na * nb)) if denom else 0.0
        child_a = float(x32[j])
        child_b = float(x32[j + m])
        pair_score = math.sqrt(max(child_a, 0.0) * max(child_b, 0.0)) * max(phase_cos, 0.0)
        rows.append(
            Spike(
                p=p,
                m=m,
                index=int(j),
                fine=float(fine[j]),
                x64=float(x64[j]),
                lift32=float(lifted[j]),
                child_a=child_a,
                child_b=child_b,
                phase_cos=phase_cos,
                pair_score=pair_score,
                exact_mgf=exact_mgf,
            )
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine", type=float, default=8.0)
    parser.add_argument("--sort", choices=["fine", "pair_score", "phase_cos", "mgf"], default="fine")
    parser.add_argument("--top", type=int, default=40)
    args = parser.parse_args()

    rows = [
        row
        for m in range(args.min_index, args.max_index + 1)
        for row in spikes_for_m(m, args.chunk, args.top_per_row, args.min_fine)
    ]
    key = {
        "fine": lambda row: row.fine,
        "pair_score": lambda row: row.pair_score,
        "phase_cos": lambda row: row.phase_cos,
        "mgf": lambda row: row.exact_mgf,
    }[args.sort]
    rows.sort(key=key, reverse=True)

    print(
        f"R263 n=64 child phase alignment spikes={len(rows)} "
        f"M=[{args.min_index},{args.max_index}] min_fine={args.min_fine} sort={args.sort}"
    )
    print("score    fine    X64     lift32  childA  childB  cos     pair    mgf     idx    M      p")
    print("-" * 112)
    for row in rows[: args.top]:
        print(
            f"{key(row):<8.4f} {row.fine:<7.3f} {row.x64:<7.3f} {row.lift32:<7.3f} "
            f"{row.child_a:<7.3f} {row.child_b:<7.3f} {row.phase_cos:<7.4f} "
            f"{row.pair_score:<7.3f} {row.exact_mgf:<7.4f} {row.index:<6d} "
            f"{row.m:<6d} {row.p}"
        )

    if rows:
        cos_vals = np.array([row.phase_cos for row in rows], dtype=float)
        pair_vals = np.array([row.pair_score for row in rows], dtype=float)
        fine_vals = np.array([row.fine for row in rows], dtype=float)
        corr = float(np.corrcoef(fine_vals, pair_vals)[0, 1]) if len(rows) > 1 else 1.0
        print("\nsummary")
        print(f"max_fine={max(row.fine for row in rows):.8f}")
        print(f"min_phase_cos={cos_vals.min():.8f} median_phase_cos={np.median(cos_vals):.8f}")
        print(f"min_pair_score={pair_vals.min():.8f} corr_fine_pair={corr:.8f}")
        print(f"phase_cos_ge_0.9={int(np.sum(cos_vals >= 0.9))}/{len(rows)}")


if __name__ == "__main__":
    main()
