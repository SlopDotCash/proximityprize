#!/usr/bin/env python3
"""#466 R241: model envelopes for the trim-five residual CDF.

R238/R240 show that the live top-five route is gated by one delicate residual
tail:

    #{X_res >= theta} / M <= 0.6012 * exp(-theta/2), theta >= 0.75.

This probe asks whether that half-rate envelope is locally forced by the cached
quotient spectra, and whether a simple one-parameter distributional model gives
an honest theorem-shaped target for the residual CDF after deleting the top five
quotient orbits.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import mpmath as mp  # noqa: E402
import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def gamma_mean_one_survival(k: float, theta: float) -> float:
    """Survival of Gamma(shape=k, scale=1/k), which has mean one."""

    x = k * theta
    return float(mp.gammainc(k, x, mp.inf) / mp.gamma(k))


def empirical_survival(case, trim: int, theta: float) -> tuple[float, int]:
    residual = case.desc[min(trim, len(case.desc)) :]
    count = int(np.count_nonzero(residual >= theta))
    return count / case.m, count


def worst_empirical_rows(cases, trim: int, theta: float) -> list[tuple]:
    rows = []
    for case in cases:
        surv, count = empirical_survival(case, trim, theta)
        half_scaled = surv * math.exp(theta / 2.0)
        rows.append((surv, half_scaled, count, case.m, case.n, case.p, case.label))
    rows.sort(reverse=True)
    return rows


def required_exponential_constant(cases, trim: int, rate: float, tau: float) -> tuple:
    """Worst A in survival(theta) <= A * exp(-rate*theta), theta >= tau."""

    best = (0.0, tau, 0, 0, 0, 0, "")
    for case in cases:
        residual = case.desc[min(trim, len(case.desc)) :]
        for idx, x0 in enumerate(residual, start=1):
            theta = float(x0)
            if theta < tau:
                break
            a_req = (idx / case.m) * math.exp(rate * theta)
            row = (a_req, theta, idx, case.m, case.n, case.p, case.label)
            if row > best:
                best = row
    return best


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
    parser.add_argument("--tau", type=float, default=0.75)
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument(
        "--thetas",
        type=float,
        nargs="+",
        default=[0.75, 0.8, 0.875, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0],
    )
    parser.add_argument(
        "--gamma-shapes",
        type=float,
        nargs="+",
        default=[0.5, 0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.9, 1.0],
    )
    parser.add_argument(
        "--rates",
        type=float,
        nargs="+",
        default=[0.25, 0.375, 0.5, 0.625, 0.75, 1.0],
    )
    parser.add_argument("--top", type=int, default=8)
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

    print(
        f"R241 residual CDF model fit cases={len(cases)} trim={args.trim} "
        f"tau={args.tau} target_C={args.target_c}"
    )

    print("\nempirical worst survival by threshold")
    print("theta   surv      half_C    slack     count  M      n     p          label")
    print("-" * 98)
    for theta in args.thetas:
        surv, half_c, count, m, n, p, label = worst_empirical_rows(cases, args.trim, theta)[0]
        print(
            f"{theta:<7.3f} {surv:<9.6f} {half_c:<9.6f} {args.target_c-half_c:<9.6f} "
            f"{count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
        )

    print("\ngamma(shape, mean=1) survival compared to empirical worst")
    header = "shape  " + " ".join(f"t={theta:g}" for theta in args.thetas[:7]) + "  max(emp-gamma)"
    print(header)
    print("-" * len(header))
    empirical_by_theta = [worst_empirical_rows(cases, args.trim, theta)[0][0] for theta in args.thetas[:7]]
    for k in args.gamma_shapes:
        gamma_vals = [gamma_mean_one_survival(k, theta) for theta in args.thetas[:7]]
        max_gap = max(e - g for e, g in zip(empirical_by_theta, gamma_vals))
        vals = " ".join(f"{g:.4f}" for g in gamma_vals)
        print(f"{k:<6.3f} {vals}  {max_gap:+.6f}")

    print("\nexponential envelope constants survival <= A exp(-rate theta), theta >= tau")
    print("rate    A_req     budget_proxy  theta     count  M      n     p          label")
    print("-" * 100)
    for rate in args.rates:
        a_req, theta, count, m, n, p, label = required_exponential_constant(
            cases, args.trim, rate, args.tau
        )
        budget_proxy = a_req * math.exp(-rate * args.tau) / rate
        print(
            f"{rate:<7.3f} {a_req:<9.6f} {budget_proxy:<13.6f} {theta:<9.6f} "
            f"{count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
        )

    print("\ntop empirical rows at tau")
    print("surv      half_C    slack     count  M      n     p          label")
    print("-" * 90)
    for surv, half_c, count, m, n, p, label in worst_empirical_rows(
        cases, args.trim, args.tau
    )[: args.top]:
        print(
            f"{surv:<9.6f} {half_c:<9.6f} {args.target_c-half_c:<9.6f} "
            f"{count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
        )


if __name__ == "__main__":
    main()
