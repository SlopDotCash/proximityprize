#!/usr/bin/env python3
"""#466 R175: random-phase controls for the dyadic bulk law.

R173/R174 suggest the dyadic bulk behaves like a two-dimensional random walk
while the arithmetic high tail is heavier.  This probe compares exact dyadic
coset spectra with random sums of n independent unit phases, normalized by
their mean square.
"""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    subgroup,
)
from scripts.probes.probe_r169_finite_grid_mgf_certificate import certificate_ratio  # noqa: E402

random.seed(466175)


def dyadic_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def random_phase_values(n: int, samples: int) -> list[float]:
    vals = []
    for _ in range(samples):
        sr = 0.0
        si = 0.0
        for _ in range(n):
            a = random.random() * 2.0 * math.pi
            sr += math.cos(a)
            si += math.sin(a)
        vals.append((sr * sr + si * si) / n)
    mean = sum(vals) / len(vals)
    return [x / mean for x in vals]


def stats(xs: list[float]) -> dict[str, float]:
    ys = sorted(xs)
    m = len(ys)

    def q(a: float) -> float:
        return ys[min(m - 1, max(0, round(a * (m - 1))))]

    def surv(t: float) -> float:
        return sum(1 for x in ys if x >= t) / m

    grid_ratio, mgf = certificate_ratio(ys, 0.5, math.ceil(max(ys) + 1))
    r170 = max(surv(k / 2) / (0.75 * math.exp(-0.25 * (k / 2))) for k in range(2, 65))
    return {
        "q50": q(0.50),
        "q75": q(0.75),
        "q90": q(0.90),
        "s1": surv(1.0),
        "s2": surv(2.0),
        "s4": surv(4.0),
        "max": ys[-1],
        "mgf": mgf,
        "grid": grid_ratio,
        "r170": r170,
    }


def fmt(label: str, st: dict[str, float]) -> str:
    return (
        f"{label:<10s} q50={st['q50']:.3f} q75={st['q75']:.3f} q90={st['q90']:.3f} "
        f"S1={st['s1']:.3f} S2={st['s2']:.3f} S4={st['s4']:.3f} "
        f"max={st['max']:.3f} mgf={st['mgf']:.4f} grid={st['grid']:.4f} r170={st['r170']:.4f}"
    )


def main() -> None:
    cases = [(64, 16778497), (128, 268437889), (256, 16777729)]
    print("exact dyadic vs random phase controls")
    print("-" * 120)
    for n, p in cases:
        dy = stats(dyadic_values(p, n))
        rp = stats(random_phase_values(n, samples=min(300_000, max(50_000, (p - 1) // n))))
        print(f"n={n} p={p}")
        print("  " + fmt("dyadic", dy))
        print("  " + fmt("random", rp))
        print(
            "  deltas "
            f"S1={dy['s1']-rp['s1']:+.4f} S2={dy['s2']-rp['s2']:+.4f} "
            f"S4={dy['s4']-rp['s4']:+.4f} mgf={dy['mgf']-rp['mgf']:+.4f}"
        )


if __name__ == "__main__":
    main()
