#!/usr/bin/env python3
"""#466 R265: parametric bulk dominance for trim-five residual spectra.

R255 showed the residual q60 is below Exp(1).  This probe searches for simple
parametric CDF envelopes (Gamma/Weibull with mean one) that upper-bound the
observed survival on the micro-band and nearby lower-bulk thresholds.
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


def gamma_survival_mean_one(k: float, theta: float) -> float:
    return float(mp.gammainc(k, k * theta, mp.inf) / mp.gamma(k))


def weibull_survival_mean_one(k: float, theta: float) -> float:
    # Weibull(shape=k, scale=lambda) with mean lambda*Gamma(1+1/k)=1.
    lam = 1.0 / float(mp.gamma(1.0 + 1.0 / k))
    return math.exp(-((theta / lam) ** k))


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
    parser.add_argument(
        "--thetas",
        type=float,
        nargs="+",
        default=[0.5, 0.625, 0.75, 0.755, 0.8, 0.875, 1.0, 1.25],
    )
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

    empirical = []
    for theta in args.thetas:
        best = 0.0
        arg = None
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            s = int(np.count_nonzero(residual >= theta)) / case.m
            if s > best:
                best = s
                arg = (case.n, case.p, case.m)
        empirical.append((theta, best, arg))

    print(f"R265 parametric bulk dominance cases={len(cases)} trim={args.trim}")
    print("\nempirical envelope")
    print("theta   Smax     arg(n,p,M)")
    print("-" * 48)
    for theta, best, arg in empirical:
        print(f"{theta:<7.3f} {best:<8.6f} {arg[0]},{arg[1]},{arg[2]}")

    gamma_shapes = [0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8, 1.0]
    weibull_shapes = [0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.9, 1.0, 1.25]

    print("\ngamma mean-one survival minus empirical")
    print("shape   minSlack theta@min maxExcess")
    print("-" * 56)
    for k in gamma_shapes:
        slacks = [(gamma_survival_mean_one(k, theta) - best, theta) for theta, best, _ in empirical]
        min_slack, theta_min = min(slacks)
        max_excess = max(-s for s, _ in slacks)
        print(f"{k:<7.3f} {min_slack:<9.6f} {theta_min:<9.3f} {max_excess:<9.6f}")

    print("\nweibull mean-one survival minus empirical")
    print("shape   minSlack theta@min maxExcess")
    print("-" * 56)
    for k in weibull_shapes:
        slacks = [(weibull_survival_mean_one(k, theta) - best, theta) for theta, best, _ in empirical]
        min_slack, theta_min = min(slacks)
        max_excess = max(-s for s, _ in slacks)
        print(f"{k:<7.3f} {min_slack:<9.6f} {theta_min:<9.3f} {max_excess:<9.6f}")

    print("\nselected envelopes")
    for label, fn, shape in [
        ("gamma", gamma_survival_mean_one, 0.65),
        ("gamma", gamma_survival_mean_one, 0.7),
        ("weibull", weibull_survival_mean_one, 0.75),
        ("weibull", weibull_survival_mean_one, 0.8),
    ]:
        print(f"{label} shape={shape}")
        for theta, best, _ in empirical:
            model = fn(shape, theta)
            print(f"  theta={theta:<5.3f} model={model:.6f} empirical={best:.6f} slack={model-best:+.6f}")


if __name__ == "__main__":
    main()
