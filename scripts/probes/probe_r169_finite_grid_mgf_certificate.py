#!/usr/bin/env python3
"""#466 R169: finite-grid certificates for the R168 MGF residual.

R168 reduced the dyadic tail route to a finite threshold grid: if staircase
increments dominate exp(t/8) and the survival-count-weighted sum is <= 2M,
then the dyadic MGF residual holds.  This probe builds such staircases and
checks their exact weighted sums on adversarial dyadic spectra.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    is_prime,
    subgroup,
)


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def grid(step: float, tmax: float) -> list[float]:
    out = [0.0]
    k = 1
    while k * step <= tmax + 1e-12:
        out.append(k * step)
        k += 1
    if out[-1] < tmax:
        out.append(tmax)
    return out


def certificate_ratio(xs: list[float], step: float, tmax: float, rate: float = 1 / 8) -> tuple[float, float]:
    """Return weighted staircase ratio and direct MGF average.

    We use increments δ_j = exp(rate*θ_{j+1}) - exp(rate*θ_j) at threshold θ_j.
    For x in [θ_j, θ_{j+1}], the staircase reaches exp(rate*θ_{j+1}), so it
    dominates exp(rate*x).  A final threshold above max(xs) is enough.
    """

    ts = grid(step, tmax)
    if ts[-1] <= max(xs):
        ts.append(max(xs) + step)
    weighted = len(xs) * math.exp(rate * ts[0])
    for j in range(len(ts) - 1):
        delta = math.exp(rate * ts[j + 1]) - math.exp(rate * ts[j])
        count = sum(1 for x in xs if x >= ts[j])
        weighted += delta * count
    mgf = sum(math.exp(rate * x) for x in xs) / len(xs)
    return weighted / len(xs), mgf


def main() -> None:
    cases = [
        (32, 32993, "spike"),
        (32, 1048609, "control"),
        (64, 264769, "spike"),
        (64, 16778497, "spike"),
        (64, 16777601, "control"),
        (128, 2101249, "small-spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
    ]
    print("n   p          kind        maxX    mgf       grid0.5   grid0.25  grid0.125")
    print("-" * 86)
    worst = (0.0, None)
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        ratios = [certificate_ratio(xs, step, math.ceil(max(xs) + 1))[0] for step in (0.5, 0.25, 0.125)]
        mgf = sum(math.exp(x / 8) for x in xs) / len(xs)
        row_worst = max(ratios)
        if row_worst > worst[0]:
            worst = (row_worst, (n, p, kind))
        print(
            f"{n:<3d} {p:<10d} {kind:<11s} {max(xs):<7.3f} {mgf:<9.5f} "
            + " ".join(f"{r:<9.5f}" for r in ratios)
        )

    print("\nsummary")
    print(f"worst_grid_ratio={worst[0]:.6f} at n={worst[1][0]} p={worst[1][1]} kind={worst[1][2]}")
    print("target <= 2.0")

    stress = []
    for n in (8, 16, 32, 64, 128):
        count = 8 if n <= 64 else 3
        for start in (max(257, n**2), n**3, n**4):
            for p in next_primes_congruent_one(n, start, count):
                if p > 350_000_000:
                    continue
                xs = normalized_values(p, n)
                ratio, mgf = certificate_ratio(xs, 0.5, math.ceil(max(xs) + 1))
                stress.append((ratio, mgf, n, p, max(xs)))
    stress.sort(reverse=True)
    print("\nstress grid0.5")
    for ratio, mgf, n, p, max_x in stress[:10]:
        print(f"  ratio={ratio:.6f} mgf={mgf:.6f} n={n} p={p} maxX={max_x:.3f}")
    print(f"stress tested={len(stress)} violations={sum(1 for r, *_ in stress if r > 2.0 + 1e-9)}")


if __name__ == "__main__":
    main()
