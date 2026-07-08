#!/usr/bin/env python3
"""#466 R174: compare dyadic bulk tails to simple distribution models.

R173 found a stable bulk law for X=|η|^2/σ^2.  This probe compares survival
fractions P[X>=T] against exponential tails exp(-λT) and the R170 envelope to
look for a proof-useful stochastic domination statement.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    subgroup,
)


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return sorted(m / sigma2 for m in mags)


def survival(xs: list[float], t: float) -> float:
    return sum(1 for x in xs if x >= t) / len(xs)


def model_error(xs: list[float], lam: float, thresholds: list[float]) -> tuple[float, float, float]:
    ratios = []
    diffs = []
    for t in thresholds:
        obs = survival(xs, t)
        pred = math.exp(-lam * t)
        ratios.append(obs / pred if pred else float("inf"))
        diffs.append(abs(obs - pred))
    return max(ratios), max(diffs), sum(diffs) / len(diffs)


def domination_prefactor(xs: list[float], lam: float) -> float:
    """Smallest A with P[X >= T] <= A exp(-lam*T) at all observed atoms."""
    desc = sorted(xs, reverse=True)
    m = len(desc)
    return max(((i + 1) / m) * math.exp(lam * x) for i, x in enumerate(desc))


def main() -> None:
    cases = [
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
        (512, 262657, "high-order"),
    ]
    thresholds = [i / 4 for i in range(2, 49)]  # 0.5..12
    lambdas = [0.5, 0.6, 0.7, 0.75, 0.8, 1.0]
    print("n   p          kind        best_lambda max_ratio max_abs mean_abs r170_ratio")
    print("-" * 92)
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        scored = [(model_error(xs, lam, thresholds), lam) for lam in lambdas]
        scored.sort(key=lambda item: item[0][2])
        (max_ratio, max_abs, mean_abs), lam = scored[0]
        r170_ratio = max(
            survival(xs, t) / (0.75 * math.exp(-0.25 * t))
            for t in [i / 2 for i in range(2, 65)]
        )
        print(
            f"{n:<3d} {p:<10d} {kind:<11s} {lam:<11.3g} "
            f"{max_ratio:<9.4f} {max_abs:<7.4f} {mean_abs:<8.4f} {r170_ratio:.4f}"
        )
        print(
            "  exp1 "
            + " ".join(
                f"T{t:g}:{survival(xs,t):.3f}/{math.exp(-t):.3f}"
                for t in (0.5, 1, 1.5, 2, 3, 4)
            )
        )
        print(
            "  exp0.75 "
            + " ".join(
                f"T{t:g}:{survival(xs,t):.3f}/{math.exp(-0.75*t):.3f}"
                for t in (0.5, 1, 1.5, 2, 3, 4)
            )
        )
        print(
            "  A_lambda "
            + " ".join(
                f"{lam:g}:{domination_prefactor(xs, lam):.3g}"
                for lam in (0.25, 0.35, 0.43, 0.5, 0.6, 0.75, 1.0)
            )
        )


if __name__ == "__main__":
    main()
