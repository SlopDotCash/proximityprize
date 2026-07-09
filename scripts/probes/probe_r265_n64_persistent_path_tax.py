#!/usr/bin/env python3
"""#466 R265: tax persistent coherent dyadic paths at n=64.

R264 showed that all dangerous n=64 fine spikes in the scanned window are
coherent along the full 8 -> 16 -> 32 -> 64 ancestry branch.  This probe asks
whether that observation gives a usable finite/structural tax: for thresholds
on best ancestors at levels 8, 16, and 32, how many n=64 rows are captured and
how much MGF mass do they carry?
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r264_n64_multilevel_coherence import rows_for_m  # noqa: E402


@dataclass(frozen=True)
class TaxRow:
    p: int
    m: int
    exact_mgf: float
    max_fine: float
    captured: int
    captured_mass: float
    captured_scaled: float
    total_top_mass: float
    threshold8: float
    threshold16: float
    threshold32: float


def tax_for_m(
    m: int,
    rows: list,
    cos_floor: float,
    t8: float,
    t16: float,
    t32: float,
) -> TaxRow | None:
    if not rows:
        return None
    captured = [
        row
        for row in rows
        if row.min_path_cos >= cos_floor
        and row.best8 >= t8
        and row.best16 >= t16
        and row.best32 >= t32
    ]
    total_top_mass = sum(math.exp(row.x64 / 4.0) / m for row in rows)
    captured_mass = sum(math.exp(row.x64 / 4.0) / m for row in captured)
    return TaxRow(
        p=rows[0].p,
        m=m,
        exact_mgf=rows[0].exact_mgf64,
        max_fine=max(row.fine64 for row in rows),
        captured=len(captured),
        captured_mass=captured_mass,
        captured_scaled=captured_mass * m,
        total_top_mass=total_top_mass,
        threshold8=t8,
        threshold16=t16,
        threshold32=t32,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--top-per-row", type=int, default=4)
    parser.add_argument("--min-fine", type=float, default=10.0)
    parser.add_argument("--cos-floor", type=float, default=0.9)
    parser.add_argument("--t8", type=float, nargs="+", default=[4.0, 5.0, 6.0, 7.0])
    parser.add_argument("--t16", type=float, nargs="+", default=[8.0, 10.0, 12.0])
    parser.add_argument("--t32", type=float, nargs="+", default=[12.0, 14.0, 16.0])
    parser.add_argument("--max-exact-mgf", type=float, default=None)
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows_by_m_raw = {
        m: rows
        for m in range(args.min_index, args.max_index + 1)
        if (rows := rows_for_m(m, args.chunk, args.top_per_row, args.min_fine))
    }
    rows_by_m = {
        m: rows
        for m, rows in rows_by_m_raw.items()
        if args.max_exact_mgf is None or rows[0].exact_mgf64 <= args.max_exact_mgf
    }
    print(
        f"R265 persistent path tax cached_rows={len(rows_by_m)} filtered_from={len(rows_by_m_raw)} "
        f"M=[{args.min_index},{args.max_index}] min_fine={args.min_fine} "
        f"top_per_row={args.top_per_row} cos_floor={args.cos_floor} "
        f"max_exact_mgf={args.max_exact_mgf}"
    )

    candidates: list[tuple[float, TaxRow]] = []
    for t8 in args.t8:
        for t16 in args.t16:
            for t32 in args.t32:
                rows = [
                    row
                    for m, path_rows in rows_by_m.items()
                    if (
                        row := tax_for_m(
                            m,
                            path_rows,
                            args.cos_floor,
                            t8,
                            t16,
                            t32,
                        )
                    )
                    is not None
                ]
                if not rows:
                    continue
                worst_mass = max(rows, key=lambda row: row.captured_mass)
                total_captured = sum(row.captured for row in rows)
                max_exact_mgf = max(row.exact_mgf for row in rows)
                score = worst_mass.captured_mass
                candidates.append((score, worst_mass))
                print(
                    f"thresholds t8={t8:.1f} t16={t16:.1f} t32={t32:.1f} "
                    f"rows={len(rows)} captured={total_captured} "
                    f"worstCapturedMass={worst_mass.captured_mass:.8f} "
                    f"worstScaled={worst_mass.captured_scaled:.4f} "
                    f"worstM={worst_mass.m} maxExactMGF={max_exact_mgf:.4f}"
                )

    candidates.sort(key=lambda pair: pair[0], reverse=True)
    print("\nR265 persistent path tax worst captured rows")
    print("mass      scaled  cap maxFine mgf     t8   t16  t32  M      p")
    print("-" * 92)
    for _, row in candidates[: args.top]:
        print(
            f"{row.captured_mass:<9.6f} {row.captured_scaled:<7.3f} {row.captured:<3d} "
            f"{row.max_fine:<7.3f} {row.exact_mgf:<7.4f} {row.threshold8:<4.1f} "
            f"{row.threshold16:<4.1f} {row.threshold32:<4.1f} {row.m:<6d} {row.p}"
        )


if __name__ == "__main__":
    main()
