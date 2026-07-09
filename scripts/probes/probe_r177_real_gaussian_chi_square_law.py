#!/usr/bin/env python3
"""#466 R177: dyadic normalized period squares match chi-square(1).

R175/R176 showed dyadic spectra are polarized relative to complex random
phases.  The right comparison is real Gaussian, because -1 in the dyadic
subgroup makes the Gauss periods real.  This probe compares

  X_C = |eta_C|^2 / sigma^2

to chi-square with one degree of freedom:

  P[Z^2 >= T] = erfc(sqrt(T/2)).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r174_bulk_distribution_model import (  # noqa: E402
    normalized_values,
    survival,
)


def chi1_survival(t: float) -> float:
    return math.erfc(math.sqrt(t / 2))


def main() -> None:
    cases = [
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
        (512, 262657, "high-order"),
    ]
    thresholds = [0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4, 6, 8]
    print(
        "chi2_1 survival: "
        + " ".join(f"T{t:g}:{chi1_survival(t):.3f}" for t in thresholds[:8])
    )
    print("n   p          kind        maxerr  meanerr  comparison")
    print("-" * 92)
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        errors = [abs(survival(xs, t) - chi1_survival(t)) for t in thresholds]
        comparison = " ".join(
            f"T{t:g}:{survival(xs,t):.3f}/{chi1_survival(t):.3f}"
            for t in (0.5, 1, 2, 4, 8)
        )
        print(
            f"{n:<3d} {p:<10d} {kind:<11s} "
            f"{max(errors):<7.4f} {sum(errors)/len(errors):<8.4f} {comparison}"
        )


if __name__ == "__main__":
    main()
