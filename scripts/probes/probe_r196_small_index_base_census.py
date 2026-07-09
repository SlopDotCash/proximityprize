#!/usr/bin/env python3
"""#466 R196: exact small-index base census for the R194 spike target.

R194 showed that the large-index range M >= 32 has comfortable spike slack,
while tiny index cases can exceed the crude R191 spike-ratio target.  This
probe exhausts dyadic cases with M = (p-1)/n < 32:

    p = M*n + 1 prime, n = 2^a.

It reports exact spectra, MGF(1/4), R189 weighted budget, and the spike ratio
exp(max(X)/4)/M.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r186_mgf_quarter_stress import (  # noqa: E402
    mgf,
    normalized_values,
)
from scripts.probes.probe_r189_bulk_plus_spikes_tail import layercake_budget  # noqa: E402
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import is_prime  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-a", type=int, default=12, help="test n=2^a through this exponent")
    parser.add_argument("--max-index", type=int, default=31)
    args = parser.parse_args()

    rows = []
    for a in range(3, args.max_a + 1):
        n = 2**a
        for m in range(2, args.max_index + 1):
            p = m * n + 1
            if is_prime(p):
                xs = normalized_values(p, n)
                max_x = max(xs)
                ratio = math.exp(max_x / 4) / len(xs)
                budget, _ = layercake_budget(xs, c_bulk=0.6, spike_budget=2, step=0.5)
                rows.append((ratio, budget, mgf(xs, 1 / 4), max_x, len(xs), n, p, a, m))

    rows.sort(reverse=True)
    target = 0.3995710770903309 / 2
    print(f"R196 small-index base census: tested={len(rows)} target={target:.6f}")
    print("ratio     budget   mgf1/4  maxX    M    n      p        a   index")
    print("-" * 82)
    for ratio, budget, mgf4, max_x, m, n, p, a, idx in rows:
        marker = "VIOL" if ratio > target + 1e-12 else "ok"
        print(
            f"{ratio:<9.6f} {budget:<8.4f} {mgf4:<7.4f} {max_x:<7.3f} "
            f"{m:<4d} {n:<6d} {p:<8d} {a:<3d} {idx:<5d} {marker}"
        )

    print("\nsummary")
    print(f"violations_target={sum(1 for r in rows if r[0] > target + 1e-12)}")
    if rows:
        worst = rows[0]
        print(
            "worst_ratio="
            f"{worst[0]:.6f} budget={worst[1]:.6f} mgf1/4={worst[2]:.6f} "
            f"maxX={worst[3]:.6f} M={worst[4]} n={worst[5]} p={worst[6]}"
        )
        print(f"worst_budget={max(rows, key=lambda r: r[1])[1]:.6f}")


if __name__ == "__main__":
    main()
