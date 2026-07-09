#!/usr/bin/env python3
"""#466 R190: dyadic tail split and product-budget anatomy.

R188/R189 showed that the largest parent spikes are aligned two-child merges,
but moderate parent tails are often inherited from one child.  This probe
tests the more precise split needed for a recursive proof:

  parent >= T -> one child >= aT OR both children >= (1-a)T.

It also measures the R168 tower product budget directly and decomposes its
mass by that split.  A viable proof route needs the inherited part to recurse
and the balanced part to be controlled by angle/mixed equidistribution.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def normalized(vals: list[complex]) -> list[float]:
    sigma = sum(abs(z) ** 2 for z in vals) / len(vals)
    return [abs(z) ** 2 / sigma for z in vals]


def transition_rows(p: int, n: int) -> list[str]:
    parent = period_by_coset_index(p, n)
    child = period_by_coset_index(p, n // 2)
    px = normalized(parent)
    cx = normalized(child)
    step = (p - 1) // n
    pairs = [(px[j], cx[j], cx[j + step], child[j].real, child[j + step].real) for j in range(len(px))]

    product_budget = sum(math.exp(l / 8) * math.exp(r / 8) for _, l, r, _, _ in pairs) / len(pairs)
    parent_mgf = sum(math.exp(x / 8) for x, *_ in pairs) / len(pairs)
    rows = [
        f"n={n} p={p} cosets={len(pairs)} parentMGF1/8={parent_mgf:.6f} "
        f"productBudget={product_budget:.6f}"
    ]
    rows.append("T a tail inherited balanced aligned_bal budget_tail budget_inh budget_bal")
    for T in (4, 6, 8, 10, 12, 16, 20):
        tail = [row for row in pairs if row[0] >= T]
        if not tail:
            continue
        for a in (0.55, 0.60, 0.67, 0.75, 0.80, 0.90):
            b = 1.0 - a
            inherited = [row for row in tail if max(row[1], row[2]) >= a * T]
            balanced = [row for row in tail if row[1] >= b * T and row[2] >= b * T]
            aligned_bal = [row for row in balanced if row[3] * row[4] >= 0]
            budget_tail = sum(math.exp(row[1] / 8) * math.exp(row[2] / 8) for row in tail) / len(pairs)
            budget_inh = sum(math.exp(row[1] / 8) * math.exp(row[2] / 8) for row in inherited) / len(pairs)
            budget_bal = sum(math.exp(row[1] / 8) * math.exp(row[2] / 8) for row in balanced) / len(pairs)
            rows.append(
                f"{T:<2g} {a:.2f} {len(tail):<6d} {len(inherited)/len(tail):.3f} "
                f"{len(balanced)/len(tail):.3f} {len(aligned_bal)/len(tail):.3f} "
                f"{budget_tail:.5f} {budget_inh:.5f} {budget_bal:.5f}"
            )
        rows.append("")
    return rows


def main() -> None:
    cases = [(32, 1048609), (64, 16778497), (128, 268437889), (256, 16777729)]
    for n, p in cases:
        print("\n".join(transition_rows(p, n)))
        print()


if __name__ == "__main__":
    main()
