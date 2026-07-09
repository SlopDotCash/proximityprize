#!/usr/bin/env python3
"""#466 R194: logarithmic max bound for the R193 spike-mass target.

R193 reduces the additive-spike side to a scalar staircase-mass certificate.
For the half-grid staircase, that mass is controlled by roughly exp(max(X)/4).
This probe asks how strong a uniform logarithmic max bound the exact spectra
support:

    max X <= 4 log M + C.

Equivalently, it measures exp(max(X)/4) / M.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r186_mgf_quarter_stress import normalized_values  # noqa: E402
from scripts.probes.probe_r189_bulk_plus_spikes_tail import case_set  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--include-huge", action="store_true")
    args = parser.parse_args()

    rows = []
    for n, p, label in sorted(case_set(include_huge=args.include_huge)):
        xs = normalized_values(p, n)
        m = len(xs)
        max_x = max(xs)
        log_defect = max_x - 4 * math.log(m)
        spike_ratio = math.exp(max_x / 4) / m
        rows.append((log_defect, spike_ratio, max_x, m, n, p, label))

    by_defect = sorted(rows, reverse=True)
    by_ratio = sorted(rows, key=lambda r: r[1], reverse=True)

    print("R194 logarithmic max-bound probe")
    print("maxX_minus_4logM  exp(max/4)/M  maxX    M       n    p          label")
    print("-" * 92)
    for defect, ratio, max_x, m, n, p, label in by_defect[:30]:
        print(f"{defect:<17.6f} {ratio:<14.6f} {max_x:<7.3f} {m:<7d} {n:<4d} {p:<10d} {label}")

    worst_defect = by_defect[0]
    worst_ratio = by_ratio[0]
    print("\nsummary")
    print(
        "worst_defect="
        f"{worst_defect[0]:.6f} ratio={worst_defect[1]:.6f} "
        f"n={worst_defect[4]} p={worst_defect[5]} label={worst_defect[6]}"
    )
    print(
        "worst_ratio="
        f"{worst_ratio[1]:.6f} defect={worst_ratio[0]:.6f} "
        f"n={worst_ratio[4]} p={worst_ratio[5]} label={worst_ratio[6]}"
    )
    for c in (-5, -4, -3, -2, -1, 0, 1):
        violations = sum(1 for defect, *_ in rows if defect > c + 1e-12)
        print(f"violations maxX <= 4 log M + {c}: {violations}")

    # R191 bulk slack is about 0.39957.  The R189 spike multiplicity is 2, so
    # the rough sufficient scalar target is exp(max/4)/M <= slack/2.
    slack = 0.3995710770903309
    target = slack / 2
    print(f"r191_spike_ratio_target={target:.6f}")
    print(f"violations target={sum(1 for _, ratio, *_ in rows if ratio > target + 1e-12)}")


if __name__ == "__main__":
    main()
