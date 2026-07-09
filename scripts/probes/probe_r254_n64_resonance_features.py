#!/usr/bin/env python3
"""#466 R254: arithmetic features of the n=64 large-index resonance family.

R253 refuted the beta-gated rank-sum window by extending the n=64 sweep.  This
probe asks whether the bad rows share simple features of M=(p-1)/64 or p:
factorization, 2-adic/3-adic valuations, generalized-Fermat forms, or residue
classes.  It is deliberately descriptive: a failed simple classifier is useful
evidence before trying a more structural resonance decomposition.
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
    mgf4: float
    top8: float
    top16: float
    max_x: float
    eighth: float
    sixteenth: float
    omega_m: int
    big_omega_m: int
    rad_m: int
    largest_factor_m: int
    v2_m: int
    v3_m: int
    m_mod_3: int
    m_mod_5: int
    m_mod_7: int
    p_mod_5: int
    p_mod_7: int
    near_square_delta: int
    near_square_abs: int


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def valuation(n: int, q: int) -> int:
    out = 0
    while n % q == 0:
        out += 1
        n //= q
    return out


def row_for_m(m: int, chunk: int) -> Row | None:
    n = 64
    p = n * m + 1
    if not is_prime(p):
        return None
    xs = normalized_values_vectorized(p, n, chunk)
    desc = np.sort(xs)[::-1]
    fm = factor(m)
    rad = 1
    for q in fm:
        rad *= q
    sqrt_m = round(math.sqrt(m))
    square_delta = m - sqrt_m * sqrt_m
    return Row(
        p=p,
        m=m,
        mgf4=float(np.exp(xs / 4.0).mean()),
        top8=float(np.exp(desc[:8] / 4.0).sum() / len(desc)),
        top16=float(np.exp(desc[:16] / 4.0).sum() / len(desc)),
        max_x=float(desc[0]),
        eighth=float(desc[7]) if len(desc) > 7 else float("nan"),
        sixteenth=float(desc[15]) if len(desc) > 15 else float("nan"),
        omega_m=len(fm),
        big_omega_m=sum(fm.values()),
        rad_m=rad,
        largest_factor_m=max(fm) if fm else m,
        v2_m=valuation(m, 2),
        v3_m=valuation(m, 3),
        m_mod_3=m % 3,
        m_mod_5=m % 5,
        m_mod_7=m % 7,
        p_mod_5=p % 5,
        p_mod_7=p % 7,
        near_square_delta=square_delta,
        near_square_abs=abs(square_delta),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--sort", choices=["top8", "top16", "mgf4", "max"], default="top8")
    args = parser.parse_args()

    rows = [row for m in range(args.min_index, args.max_index + 1) if (row := row_for_m(m, args.chunk))]
    key = {
        "top8": lambda row: row.top8,
        "top16": lambda row: row.top16,
        "mgf4": lambda row: row.mgf4,
        "max": lambda row: row.max_x,
    }[args.sort]
    rows.sort(key=key, reverse=True)

    print(f"R254 n=64 resonance features cases={len(rows)} M=[{args.min_index},{args.max_index}] sort={args.sort}")
    print(
        "score    top8    top16   mgf4    maxX    x8      x16     M      p       "
        "omega Omega lpf    v2 v3 M%3 M%5 M%7 p%5 p%7 sqDelta |sqD|"
    )
    print("-" * 132)
    for row in rows[: args.top]:
        print(
            f"{key(row):<8.4f} {row.top8:<7.4f} {row.top16:<7.4f} {row.mgf4:<7.4f} "
            f"{row.max_x:<7.3f} {row.eighth:<7.3f} {row.sixteenth:<7.3f} "
            f"{row.m:<6d} {row.p:<7d} {row.omega_m:<5d} {row.big_omega_m:<5d} "
            f"{row.largest_factor_m:<6d} {row.v2_m:<2d} {row.v3_m:<2d} "
            f"{row.m_mod_3:<3d} {row.m_mod_5:<3d} {row.m_mod_7:<3d} "
            f"{row.p_mod_5:<3d} {row.p_mod_7:<3d} {row.near_square_delta:<7d} {row.near_square_abs}"
        )

    if rows:
        print("\nsummary")
        for name in ("top8", "top16", "mgf4", "max"):
            row = max(rows, key={
                "top8": lambda r: r.top8,
                "top16": lambda r: r.top16,
                "mgf4": lambda r: r.mgf4,
                "max": lambda r: r.max_x,
            }[name])
            print(
                f"max_{name}=M{row.m}_p{row.p} value={getattr(row, 'max_x' if name == 'max' else name):.8f} "
                f"omega={row.omega_m} Omega={row.big_omega_m} lpf={row.largest_factor_m} "
                f"mods=({row.m_mod_3},{row.m_mod_5},{row.m_mod_7})"
            )


if __name__ == "__main__":
    main()
