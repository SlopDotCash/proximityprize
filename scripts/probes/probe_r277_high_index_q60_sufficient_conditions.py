#!/usr/bin/env python3
"""#466 R277: sufficient-condition search for the high-index q60 cap.

R276 leaves one analytic micro-band branch:

    M >= 2048  ==>  q60(trim-five residual) <= 0.759

or equivalently a slightly weaker S(0.75) cap.  This probe looks for smoother
bulk quantities that imply the q60 cap on observed high-index cases, since
partial sums and lower-bulk averages are closer to standard analytic estimates
than a single order statistic.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import is_prime  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import cached_desc  # noqa: E402


@dataclass(frozen=True)
class Row:
    n: int
    p: int
    m: int
    survival: float
    q55: float
    q575: float
    q60: float
    q625: float
    q65: float
    features: dict[str, float]


def feature_table(residual_desc: np.ndarray, modulus_index: int) -> dict[str, float]:
    residual_asc = residual_desc[::-1]
    out: dict[str, float] = {}
    for frac in [0.50, 0.55, 0.60, 0.65, 0.70, 0.75]:
        tag = str(int(round(frac * 100)))
        k = max(1, min(len(residual_asc), math.ceil(frac * len(residual_asc))))
        lower = residual_asc[:k]
        upper = residual_desc[:k]
        out[f"lowAvg{tag}"] = float(np.mean(lower))
        out[f"upAvg{tag}"] = float(np.mean(upper))
        out[f"lowSum{tag}"] = float(np.sum(lower) / modulus_index)
        out[f"upSum{tag}"] = float(np.sum(upper) / modulus_index)
        out[f"gapAvg{tag}"] = out[f"upAvg{tag}"] - out[f"lowAvg{tag}"]
    return out


def quantile(residual_desc: np.ndarray, q: float) -> float:
    return float(np.quantile(residual_desc, q))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[256, 512, 1024])
    parser.add_argument("--min-index", type=int, default=2048)
    parser.add_argument("--max-index", type=int, default=8000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--q60-cap", type=float, default=0.759)
    parser.add_argument("--top", type=int, default=16)
    parser.add_argument("--stride", type=int, default=1)
    parser.add_argument("--limit-per-n", type=int, default=0)
    args = parser.parse_args()

    rows: list[Row] = []
    skipped = 0
    for n in args.ns:
        tested_for_n = 0
        for m in range(args.min_index, args.max_index + 1):
            if (m - args.min_index) % args.stride != 0:
                continue
            p = m * n + 1
            if not is_prime(p):
                continue
            cached = cached_desc(p, n, args.chunk, args.cache_dir, args.cache_only)
            if cached is None:
                skipped += 1
                continue
            _xs, desc = cached
            residual = desc[min(args.trim, len(desc)) :]
            rows.append(
                Row(
                    n=n,
                    p=p,
                    m=m,
                    survival=int(np.count_nonzero(residual >= args.theta)) / m,
                    q55=quantile(residual, 0.55),
                    q575=quantile(residual, 0.575),
                    q60=quantile(residual, 0.60),
                    q625=quantile(residual, 0.625),
                    q65=quantile(residual, 0.65),
                    features=feature_table(residual, m),
                )
            )
            tested_for_n += 1
            if args.limit_per_n and tested_for_n >= args.limit_per_n:
                break

    print(f"R277 high-index q60 sufficient-condition cases={len(rows)} skipped={skipped}")
    if not rows:
        return

    by_q60 = sorted(rows, key=lambda r: r.q60, reverse=True)
    print("\nq60 frontier")
    print("q60      S075     q575     q625     lowAvg70 upAvg70  gapAvg70 n     p          M")
    print("-" * 104)
    for row in by_q60[: args.top]:
        print(
            f"{row.q60:<8.6f} {row.survival:<8.6f} {row.q575:<8.6f} {row.q625:<8.6f} "
            f"{row.features['lowAvg70']:<8.5f} {row.features['upAvg70']:<8.5f} "
            f"{row.features['gapAvg70']:<8.5f} {row.n:<5d} {row.p:<10d} {row.m}"
        )

    print("\nquantile maxima")
    for label in ["q55", "q575", "q60", "q625", "q65"]:
        row = max(rows, key=lambda r: getattr(r, label))
        print(
            f"{label:<4s} max={getattr(row, label):.8f} S075={row.survival:.8f} "
            f"n={row.n} p={row.p} M={row.m}"
        )

    feature_names = sorted(rows[0].features)
    matrix = np.array([[r.features[name] for name in feature_names] + [r.m / r.n, math.log(r.m)] for r in rows])
    names = feature_names + ["M/n", "logM"]
    q60s = np.array([r.q60 for r in rows])
    svals = np.array([r.survival for r in rows])

    print("\ncorrelations with q60")
    cors = []
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(q60s, matrix[:, idx])[0, 1])
        cors.append((abs(corr), name, corr))
    for _abs_corr, name, corr in sorted(cors, reverse=True)[:24]:
        print(f"{name:<12s} {corr:+.6f}")

    print("\ncorrelations with S(0.75)")
    scors = []
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(svals, matrix[:, idx])[0, 1])
        scors.append((abs(corr), name, corr))
    for _abs_corr, name, corr in sorted(scors, reverse=True)[:16]:
        print(f"{name:<12s} {corr:+.6f}")

    print("\none-feature monotone sufficient caps for q60")
    bad = [row for row in rows if row.q60 > args.q60_cap]
    good = [row for row in rows if row.q60 <= args.q60_cap]
    print(f"strict bad above cap {args.q60_cap:.6f}: {len(bad)}")
    for name in feature_names:
        vals = [(row.features[name], row.q60, row) for row in rows]
        high_bad = max((v for v, q, _row in vals if q > args.q60_cap), default=float("-inf"))
        high_good = max((v for v, q, _row in vals if q <= args.q60_cap), default=float("-inf"))
        low_bad = min((v for v, q, _row in vals if q > args.q60_cap), default=float("inf"))
        low_good = min((v for v, q, _row in vals if q <= args.q60_cap), default=float("inf"))
        if high_bad < high_good or low_bad > low_good:
            print(
                f"{name:<12s} badRange=[{low_bad:.8f},{high_bad:.8f}] "
                f"goodRange=[{low_good:.8f},{high_good:.8f}]"
            )

    print("\nlinear least-squares q60 model using smoother features")
    smooth = ["lowAvg60", "lowAvg65", "lowAvg70", "upAvg60", "upAvg65", "upAvg70", "gapAvg70", "logM"]
    xcols = []
    for row in rows:
        values = [1.0]
        for name in smooth:
            values.append(math.log(row.m) if name == "logM" else row.features[name])
        xcols.append(values)
    xmat = np.array(xcols)
    coeffs, *_ = np.linalg.lstsq(xmat, q60s, rcond=None)
    pred = xmat @ coeffs
    residual = q60s - pred
    print("features:", ", ".join(["const", *smooth]))
    print("coeffs:  ", " ".join(f"{c:+.6f}" for c in coeffs))
    print(f"max_abs_error={float(np.max(np.abs(residual))):.8f} rmse={float(np.sqrt(np.mean(residual**2))):.8f}")
    worst_idx = int(np.argmax(residual))
    worst = rows[worst_idx]
    print(
        f"worst_underprediction err={residual[worst_idx]:+.8f} q60={worst.q60:.8f} "
        f"pred={pred[worst_idx]:.8f} n={worst.n} p={worst.p} M={worst.m}"
    )


if __name__ == "__main__":
    main()
