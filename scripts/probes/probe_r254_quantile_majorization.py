#!/usr/bin/env python3
"""#466 R254: majorization interfaces for the trim-five q60 cap.

R253 identifies the micro-band obstruction with a trim-five residual q60
envelope.  This probe asks whether the q60 cap follows from smoother
majorization data: cumulative sums above/below quantile cuts and Lorenz-style
partial averages.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=8)
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    ps = [0.5, 0.55, 0.6, 0.65, 0.7]
    rows = []
    for case in cases:
        residual_desc = case.desc[min(args.trim, len(case.desc)) :]
        residual_asc = residual_desc[::-1]
        m = case.m
        q60 = float(np.quantile(residual_desc, 0.6))
        s075 = int(np.count_nonzero(residual_desc >= 0.75)) / m
        micro = s075 * math.exp(0.755 / 2.0)
        features = []
        for p in ps:
            k = max(1, min(len(residual_asc), math.ceil(p * len(residual_asc))))
            lower_avg = float(np.mean(residual_asc[:k]))
            upper_avg = float(np.mean(residual_desc[:k]))
            lower_sum = float(np.sum(residual_asc[:k]) / m)
            upper_sum = float(np.sum(residual_desc[:k]) / m)
            features.extend([lower_avg, upper_avg, lower_sum, upper_sum])
        rows.append((micro, q60, *features, case.n, case.p, case.m))

    rows.sort(reverse=True)
    print(f"R254 quantile majorization cases={len(rows)} trim={args.trim}")
    print("micro    q60      lowAvg60 upAvg60  lowSum60 upSum60  n     p          M")
    print("-" * 96)
    # feature offsets: for p index 2 (=0.6), lower_avg, upper_avg, lower_sum, upper_sum.
    off = 2 + 2 * 4
    for row in rows[: args.top]:
        micro, q60 = row[0], row[1]
        low_avg60, up_avg60, low_sum60, up_sum60 = row[off : off + 4]
        n, p, m = row[-3:]
        print(
            f"{micro:<8.6f} {q60:<8.6f} {low_avg60:<8.5f} {up_avg60:<8.5f} "
            f"{low_sum60:<8.5f} {up_sum60:<8.5f} {n:<5d} {p:<10d} {m}"
        )

    names = ["q60"]
    for p in ps:
        names.extend([f"lowAvg{p}", f"upAvg{p}", f"lowSum{p}", f"upSum{p}"])
    names.extend(["M/n", "logM"])
    matrix = []
    target = []
    for row in rows:
        target.append(row[0])
        m = row[-1]
        n = row[-3]
        matrix.append([row[1], *row[2:-3], m / n, math.log(m)])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)

    print("\ncorrelations with micro")
    cors = []
    for idx, name in enumerate(names):
        cors.append((abs(float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])), name, float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])))
    for _abs, name, corr in sorted(cors, reverse=True)[:20]:
        print(f"{name:<12s} {corr:+.6f}")

    print("\nmax partial averages")
    for pidx, p in enumerate(ps):
        base = 2 + pidx * 4
        low_row = max(rows, key=lambda r: r[base])
        up_row = max(rows, key=lambda r: r[base + 1])
        print(
            f"p={p:<4.2f} maxLowAvg={low_row[base]:.6f} micro={low_row[0]:.6f} "
            f"n={low_row[-3]} p={low_row[-2]} M={low_row[-1]} | "
            f"maxUpAvg={up_row[base+1]:.6f} micro={up_row[0]:.6f} "
            f"n={up_row[-3]} p={up_row[-2]} M={up_row[-1]}"
        )


if __name__ == "__main__":
    main()
