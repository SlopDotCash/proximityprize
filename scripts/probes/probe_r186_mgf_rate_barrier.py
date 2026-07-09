#!/usr/bin/env python3
"""#466 R186: MGF rate barrier for the dyadic tail route.

R184 reduces the tower product budget to a one-level child MGF at rate 1/4.
This probe checks how much rate headroom exists.  If rates slightly above 1/4
already approach or exceed the budget 2, then the tower route should target
1/4 specifically rather than a stronger exponential law.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r174_bulk_distribution_model import normalized_values  # noqa: E402


def main() -> None:
    cases = [
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
        (512, 262657, "high"),
    ]
    rates = [1 / 8, 1 / 6, 1 / 4, 1 / 3, 1 / 2]
    print("n p kind maxX " + " ".join(f"mgf{r:.3g}" for r in rates))
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        vals = [sum(math.exp(r * x) for x in xs) / len(xs) for r in rates]
        print(
            f"{n} {p} {kind} {max(xs):.3f} "
            + " ".join(f"{value:.4g}" for value in vals)
        )


if __name__ == "__main__":
    main()
