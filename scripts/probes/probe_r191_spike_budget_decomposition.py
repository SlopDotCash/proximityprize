#!/usr/bin/env python3
"""#466 R191: decompose the R189 budget into bulk and spike cost.

R190 reduces quarter-MGF to a weighted grid budget.  For the R189 half-grid
envelope

    N(T) <= (3/5) M exp(-T/2) + 2,

the infinite bulk contribution is already about 1.60043.  The remaining
question is the additive spike cost, controlled by exp(max(X)/4)/M.  This
probe measures that term on the exact spectra used by R189.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r186_mgf_quarter_stress import normalized_values  # noqa: E402
from scripts.probes.probe_r189_bulk_plus_spikes_tail import (  # noqa: E402
    case_set,
    layercake_budget,
)


def infinite_bulk_constant(step: float = 0.5, c_bulk: float = 0.6) -> float:
    """Closed form for the infinite half-grid bulk contribution."""
    q = math.exp(-step / 4)
    # base exp(step/4), plus sum over j>=2 of
    # C * (exp(jh/4)-exp((j-1)h/4)) * exp(-jh/2)
    return math.exp(step / 4) + c_bulk * (1 - q) * (q**2) / (1 - q)


def main() -> None:
    rows = []
    for n, p, label in sorted(case_set(include_huge=False)):
        xs = normalized_values(p, n)
        m = len(xs)
        max_x = max(xs)
        budget, _ = layercake_budget(xs, c_bulk=0.6, spike_budget=2, step=0.5)
        rows.append((math.exp(max_x / 4) / m, budget, max_x, m, n, p, label))

    rows.sort(reverse=True)
    bulk = infinite_bulk_constant()
    print("R191 spike-budget decomposition")
    print(f"infinite_bulk_constant={bulk:.12f}")
    print(f"infinite_bulk_slack_to_2={2 - bulk:.12f}")
    print()
    print("exp(max/4)/M  budget  maxX   M       n   p          label")
    print("-" * 84)
    for ratio, budget, max_x, m, n, p, label in rows[:30]:
        print(f"{ratio:<15.6f} {budget:<7.4f} {max_x:<6.2f} {m:<7d} {n:<3d} {p:<10d} {label}")

    worst = rows[0]
    print("\nsummary")
    print(
        "worst_spike_ratio="
        f"{worst[0]:.6f} budget={worst[1]:.6f} maxX={worst[2]:.6f} "
        f"M={worst[3]} n={worst[4]} p={worst[5]} label={worst[6]}"
    )
    print(f"worst_budget={max(rows, key=lambda r: r[1])[1]:.6f}")


if __name__ == "__main__":
    main()
