#!/usr/bin/env python3
"""#466 R243: can low moments certify the trim-five middle-bulk cap?

R242 says the live residual endpoint is a middle-bulk percentile theorem:
after deleting the top five quotient values, roughly 41.22% of the residual
mass may exceed 0.75.  This probe asks whether that cap can follow from a small
set of moment/box constraints alone.

For each cached case, we compute the exact residual moments and solve the
one-dimensional extremal problem:

    maximize P[X >= theta]

among distributions on [0, B] with the same first d moments, by linear
programming on a fine support grid.  If the LP optimum is far above the true
survival, then the moments are not the right proof interface.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def bounded_moment_survival_bound(
    moments: list[float], theta: float, cap: float, degree: int, grid_size: int
) -> tuple[float, np.ndarray]:
    """Return an LP upper bound for survival from moments on [0, cap].

    Uses scipy when available.  The grid is deliberately simple: if this
    optimistic discretized moment LP is loose, exact continuous moment theory
    will not save this route.
    """

    from scipy.optimize import linprog

    grid = np.linspace(0.0, cap, grid_size)
    c = -(grid >= theta).astype(float)
    a_eq = [np.ones_like(grid)]
    b_eq = [1.0]
    for k in range(1, degree + 1):
        a_eq.append(grid**k)
        b_eq.append(moments[k - 1])
    res = linprog(
        c,
        A_eq=np.vstack(a_eq),
        b_eq=np.array(b_eq),
        bounds=[(0.0, None)] * len(grid),
        method="highs",
    )
    if not res.success:
        return float("nan"), grid
    return -float(res.fun), grid


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
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--degree", type=int, nargs="+", default=[2, 3, 4])
    parser.add_argument("--grid-size", type=int, default=801)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()

    try:
        import scipy  # noqa: F401
    except Exception as exc:  # pragma: no cover - environment guard
        raise SystemExit(f"scipy unavailable: {exc}") from exc

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        survival = int(np.count_nonzero(residual >= args.theta)) / case.m
        cap = float(residual[0])
        max_degree = max(args.degree)
        moments = [float(np.mean(residual**k)) for k in range(1, max_degree + 1)]
        bounds = []
        for degree in args.degree:
            bound, _grid = bounded_moment_survival_bound(
                moments, args.theta, cap, degree, args.grid_size
            )
            bounds.append(bound)
        rows.append((survival, *bounds, cap, moments[0], moments[1], case.m, case.n, case.p))

    rows.sort(reverse=True)
    print(
        f"R243 middle-bulk moment LP cases={len(rows)} trim={args.trim} "
        f"theta={args.theta} grid={args.grid_size}"
    )
    deg_header = " ".join(f"LPd{d:<2d}" for d in args.degree)
    print(f"surv     {deg_header} cap      mean     second   M      n     p")
    print("-" * 92)
    for row in rows[: args.top]:
        survival = row[0]
        bounds = row[1 : 1 + len(args.degree)]
        cap, mean, second, m, n, p = row[1 + len(args.degree) :]
        print(
            f"{survival:<8.6f} "
            + " ".join(f"{b:<7.5f}" for b in bounds)
            + f" {cap:<8.3f} {mean:<8.5f} {second:<8.5f} {m:<6d} {n:<5d} {p}"
        )

    print("\nsummary by degree")
    for idx, degree in enumerate(args.degree, start=1):
        gaps = [row[idx] - row[0] for row in rows if not math.isnan(row[idx])]
        print(
            f"degree={degree} min_gap={min(gaps):.6f} median_gap={float(np.median(gaps)):.6f} "
            f"max_gap={max(gaps):.6f}"
        )


if __name__ == "__main__":
    main()
