#!/usr/bin/env python3
"""#466 R231: top-spike trimmed quotient MGF feasibility.

R230 showed that a one-piece low-band exponential survival envelope is too
expensive: rare high-threshold multi-spike clusters force a huge bulk constant.
This probe tests the next residual shape:

* pay the top `L` quotient orbits exactly;
* prove an exponential tail only for the remaining quotient spectrum;
* add the exact top-spike MGF contribution to the residual envelope budget.

The output is empirical/formal-design evidence, not a theorem: it identifies
whether a top-spike classification lemma would be enough to recover the
quarter-MGF target.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r217_normalized_sq_grid_budget import staircase_deltas  # noqa: E402
from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)


@dataclass(frozen=True)
class Case:
    n: int
    p: int
    m: int
    xs: np.ndarray
    desc: np.ndarray
    label: str


def cached_desc(
    p: int, n: int, chunk: int, cache_dir: Path | None, cache_only: bool
) -> tuple[np.ndarray, np.ndarray] | None:
    if cache_dir is None:
        if cache_only:
            return None
        xs = normalized_values_vectorized(p, n, chunk)
        return xs, np.sort(xs)[::-1]
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = cache_dir / f"r231_n{n}_p{p}_chunk{chunk}.npz"
    if path.exists():
        try:
            with np.load(path) as data:
                desc = data["desc"]
            return desc[::-1], desc
        except (EOFError, OSError, ValueError, KeyError):
            path.unlink(missing_ok=True)
            if cache_only:
                return None
    if cache_only:
        return None
    xs = normalized_values_vectorized(p, n, chunk)
    desc = np.sort(xs)[::-1]
    np.savez_compressed(path, desc=desc)
    return xs, desc


def medium_cases(
    min_a: int,
    max_a: int,
    max_index: int,
    min_index: int,
    chunk: int,
    cache_dir: Path | None,
    cache_only: bool,
) -> list[Case]:
    out: list[Case] = []
    for a in range(min_a, max_a + 1):
        n = 2**a
        for m in range(max(2, min_index), max_index + 1):
            p = m * n + 1
            if is_prime(p):
                cached = cached_desc(p, n, chunk, cache_dir, cache_only)
                if cached is None:
                    continue
                xs, desc = cached
                out.append(Case(n, p, m, xs, desc, f"a={a}-M={m}"))
    return out


def residual_required_c(
    xs: np.ndarray, tau: float, spike_budget: float, trim: int
) -> tuple[float, float, int]:
    desc = xs
    residual = desc[min(trim, len(desc)) :]
    m = len(desc)
    best_c = 0.0
    best_theta = tau
    best_count = 0
    for idx, x0 in enumerate(residual):
        theta = float(x0)
        if theta <= tau:
            break
        count = idx + 1
        c_req = max(0.0, (count - spike_budget) / m) * math.exp(theta / 2.0)
        if c_req > best_c:
            best_c = c_req
            best_theta = theta
            best_count = count
    return best_c, best_theta, best_count


def top_stair_budget_per_carrier(
    xs: np.ndarray, trim: int, step: float, cutoff: float, rate: float
) -> float:
    desc = xs
    top = desc[: min(trim, len(desc))]
    if len(top) == 0:
        return 0.0
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        total += delta * int(np.count_nonzero(top >= theta))
    return total / len(desc)


def residual_envelope_budget(
    carrier: int,
    step: float,
    cutoff: float,
    rate: float,
    tau: float,
    c_bulk: float,
    spike_budget: float,
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if theta <= tau + 1.0e-15:
            bound = 1.0
        else:
            bound = c_bulk * math.exp(-theta / 2.0) + spike_budget / carrier
        total += delta * bound
    return total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=3)
    parser.add_argument("--medium-max-a", type=int, default=8)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--cache-dir", type=Path, default=None)
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trims", type=int, nargs="+", default=[1, 2, 4, 8, 16, 32])
    parser.add_argument("--taus", type=float, nargs="+", default=[0.5, 1.0, 2.0])
    parser.add_argument("--spike-budgets", type=float, nargs="+", default=[0.0, 1.0, 2.0])
    parser.add_argument("--step", type=float, default=0.25)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--cutoff", type=float, default=0.0)
    parser.add_argument("--top", type=int, default=30)
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
    rows = []
    for trim in args.trims:
        for tau in args.taus:
            for spike_budget in args.spike_budgets:
                worst = (0.0, tau, 0, None)
                for case in cases:
                    c_req, theta, count = residual_required_c(case.desc, tau, spike_budget, trim)
                    if c_req > worst[0]:
                        worst = (c_req, theta, count, case)
                worst_budget = -1.0
                worst_budget_case = None
                for case in cases:
                    cutoff = max(args.cutoff, float(case.xs.max()))
                    budget = top_stair_budget_per_carrier(
                        case.desc, trim, args.step, cutoff, args.rate
                    ) + residual_envelope_budget(
                        case.m, args.step, cutoff, args.rate, tau, worst[0], spike_budget
                    )
                    if budget > worst_budget:
                        worst_budget = budget
                        worst_budget_case = case
                rows.append(
                    (
                        worst_budget,
                        worst[0],
                        trim,
                        tau,
                        spike_budget,
                        worst[1],
                        worst[2],
                        worst[3],
                        worst_budget_case,
                    )
                )

    rows.sort(key=lambda row: (row[0], row[1]))
    print(
        "R231 top-spike trimmed MGF feasibility "
        f"cases={len(cases)} step={args.step} rate={args.rate} cutoff>={args.cutoff}"
    )
    print(
        "budget   slack    C_req    trim tau   K     witness_theta count "
        "Cwit(n,p,M)             Bwit(n,p,M)"
    )
    print("-" * 128)
    for budget, c_req, trim, tau, spike_budget, theta, count, ccase, bcase in rows[: args.top]:
        cdesc = "-" if ccase is None else f"{ccase.n},{ccase.p},{ccase.m}"
        bdesc = "-" if bcase is None else f"{bcase.n},{bcase.p},{bcase.m}"
        print(
            f"{budget:<8.4f} {2-budget:<8.4f} {c_req:<8.5f} {trim:<5d} "
            f"{tau:<5.2f} {spike_budget:<5.1f} {theta:<13.6f} {count:<5d} "
            f"{cdesc:<22s} {bdesc}"
        )

    print("\nsummary")
    feasible = [row for row in rows if row[0] <= 2.0 + 1e-9]
    print(f"feasible_rows={len(feasible)}")
    if rows:
        best = rows[0]
        print(
            f"best_budget={best[0]:.6f} slack={2-best[0]:.6f} "
            f"C_req={best[1]:.8f} trim={best[2]} tau={best[3]} K={best[4]}"
        )


if __name__ == "__main__":
    main()
