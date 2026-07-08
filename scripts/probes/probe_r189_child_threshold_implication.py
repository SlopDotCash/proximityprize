#!/usr/bin/env python3
"""#466 R189: child-threshold implications for parent tail events.

R188 found top spikes have two large same-sign children.  This probe checks
whether that extends to the whole high tail: does X_parent >= T force both
children to be at least a fixed fraction of T?
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def child_threshold_table(p: int, n: int) -> list[tuple[float, int, float]]:
    parent = period_by_coset_index(p, n)
    child = period_by_coset_index(p, n // 2)
    sigp = sum(abs(z) ** 2 for z in parent) / len(parent)
    sigc = sum(abs(z) ** 2 for z in child) / len(child)
    px = [abs(z) ** 2 / sigp for z in parent]
    cx = [abs(z) ** 2 / sigc for z in child]
    step = (p - 1) // n
    rows = []
    for T in (4, 6, 8, 10, 12, 16, 20):
        indices = [j for j, x in enumerate(px) if x >= T]
        if not indices:
            continue
        best = 0.0
        for c in (0.1, 0.15, 0.2, 0.25, 0.33, 0.4, 0.45):
            if all(min(cx[j], cx[j + step]) >= c * T for j in indices):
                best = c
        rows.append((T, len(indices), best))
    return rows


def main() -> None:
    cases = [(64, 16778497), (128, 268437889), (256, 16777729)]
    for n, p in cases:
        print(f"\nn {n} p {p}")
        for T, count, best in child_threshold_table(p, n):
            print(f"T {T:g} N {count} min-child fraction all>= {best:g}")


if __name__ == "__main__":
    main()
