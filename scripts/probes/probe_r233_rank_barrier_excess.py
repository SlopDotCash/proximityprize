#!/usr/bin/env python3
"""#466 R233: sorted quotient-spectrum rank-barrier scan.

For a quotient spectrum `X_q`, the quarter-MGF is

    mean_q exp(X_q / 4).

If the descending order statistics obey a power-rank barrier

    X_(r) <= 4 log(B * M / r^alpha)

with `alpha > 1`, then the rank contributions are summable directly, without
passing through an all-threshold survival envelope.  This probe measures the
empirical excess over that barrier and flags generalized-Fermat identity-coset
rows.
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
    n: int
    p: int
    m: int
    mgf4: float
    max_excess: float
    max_rank: int
    top_x: float
    gf_base: int | None


def gf_base(n: int, p: int) -> int | None:
    """Return B if p = B^(n/2)+1 exactly, otherwise None."""
    if n < 2 or n % 2:
        return None
    target = p - 1
    exp = n // 2
    b = round(target ** (1.0 / exp))
    for cand in range(max(1, b - 2), b + 3):
        if cand**exp == target:
            return cand
    return None


def rank_barrier(
    xs: np.ndarray,
    b_factor: float,
    alpha: float,
    ranks: list[int],
) -> tuple[float, int]:
    desc = np.sort(xs)[::-1]
    m = len(desc)
    worst = -float("inf")
    worst_rank = 0
    for rank in ranks:
        if rank <= 0 or rank > m:
            continue
        barrier = 4.0 * math.log(b_factor * m / (rank**alpha))
        excess = float(desc[rank - 1]) - barrier
        if excess > worst:
            worst = excess
            worst_rank = rank
    return worst, worst_rank


def medium_rows(
    max_a: int,
    max_index: int,
    min_index: int,
    chunk: int,
    b_factor: float,
    alpha: float,
    ranks: list[int],
) -> list[Row]:
    rows: list[Row] = []
    for a in range(3, max_a + 1):
        n = 2**a
        for m in range(max(2, min_index), max_index + 1):
            p = m * n + 1
            if not is_prime(p):
                continue
            xs = normalized_values_vectorized(p, n, chunk)
            excess, rank = rank_barrier(xs, b_factor, alpha, ranks)
            rows.append(
                Row(
                    n=n,
                    p=p,
                    m=m,
                    mgf4=float(np.exp(xs / 4.0).mean()),
                    max_excess=excess,
                    max_rank=rank,
                    top_x=float(xs.max()),
                    gf_base=gf_base(n, p),
                )
            )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-max-a", type=int, default=9)
    parser.add_argument("--medium-max-index", type=int, default=2048)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--b-factor", type=float, default=1.0)
    parser.add_argument("--alpha", type=float, default=1.0)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument(
        "--ranks",
        type=int,
        nargs="+",
        default=[1, 2, 4, 8, 16, 32, 64, 128, 256],
    )
    args = parser.parse_args()

    rows = medium_rows(
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.b_factor,
        args.alpha,
        args.ranks,
    )
    rows.sort(key=lambda row: row.max_excess, reverse=True)
    non_gf = [row for row in rows if row.gf_base is None]
    gf = [row for row in rows if row.gf_base is not None]

    print(
        "R233 rank-barrier excess "
        f"cases={len(rows)} non_gf={len(non_gf)} gf={len(gf)} "
        f"B={args.b_factor} alpha={args.alpha} ranks={args.ranks}"
    )
    print("excess   rank   mgf1/4  topX    M       n     p          GF")
    print("-" * 76)
    for row in rows[: args.top]:
        gf_s = "-" if row.gf_base is None else f"B={row.gf_base}"
        print(
            f"{row.max_excess:<8.3f} {row.max_rank:<6d} {row.mgf4:<7.4f} "
            f"{row.top_x:<7.3f} {row.m:<7d} {row.n:<5d} {row.p:<10d} {gf_s}"
        )

    print("\nsummary")
    if rows:
        print(
            f"worst_all={rows[0].max_excess:.6f} "
            f"n={rows[0].n} p={rows[0].p} rank={rows[0].max_rank} "
            f"gf={rows[0].gf_base}"
        )
    if non_gf:
        worst = non_gf[0]
        print(
            f"worst_non_gf={worst.max_excess:.6f} "
            f"n={worst.n} p={worst.p} rank={worst.max_rank} mgf1/4={worst.mgf4:.6f}"
        )
    if gf:
        worst = gf[0]
        print(
            f"worst_gf={worst.max_excess:.6f} "
            f"n={worst.n} p={worst.p} rank={worst.max_rank} B={worst.gf_base}"
        )


if __name__ == "__main__":
    main()
