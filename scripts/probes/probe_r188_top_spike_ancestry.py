#!/usr/bin/env python3
"""#466 R188: ancestry of top dyadic period spikes.

The no-far-spike theorem might come from the dyadic tower: a large parent
period must be assembled from large, same-sign child periods.  This probe
checks the top cosets and reports their child magnitudes and alignment.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def normalized_mags(vals: list[complex]) -> list[float]:
    sigma = sum(abs(z) ** 2 for z in vals) / len(vals)
    return [abs(z) ** 2 / sigma for z in vals]


def top_ancestry(p: int, n: int, top_k: int = 20) -> dict[str, float]:
    parent = period_by_coset_index(p, n)
    child = period_by_coset_index(p, n // 2)
    px = normalized_mags(parent)
    cx = normalized_mags(child)
    step = (p - 1) // n
    top = sorted(range(len(px)), key=lambda j: px[j], reverse=True)[:top_k]
    alignments = []
    min_child = []
    sum_ratio = []
    same_sign = 0
    for j in top:
        a = child[j].real
        b = child[j + step].real
        denom = (abs(a) + abs(b)) ** 2
        align = ((a + b) ** 2 / denom) if denom else 0.0
        alignments.append(align)
        min_child.append(min(cx[j], cx[j + step]))
        denom_sum = cx[j] + cx[j + step]
        sum_ratio.append(px[j] / denom_sum if denom_sum else 0.0)
        if a * b >= 0:
            same_sign += 1
    return {
        "max_x": px[top[0]],
        "same_sign_frac": same_sign / len(top),
        "align_min": min(alignments),
        "align_mean": sum(alignments) / len(alignments),
        "min_child_mean": sum(min_child) / len(min_child),
        "ratio_mean": sum(sum_ratio) / len(sum_ratio),
    }


def main() -> None:
    cases = [
        (32, 1048609),
        (64, 16778497),
        (128, 268437889),
        (256, 16777729),
    ]
    print("n p top maxX sameSign align[min,mean] meanMinChild meanParentOverChildSum")
    print("-" * 92)
    for n, p in cases:
        st = top_ancestry(p, n)
        print(
            f"{n:<3d} {p:<10d} 20  {st['max_x']:<8.3f} {st['same_sign_frac']:<8.3f} "
            f"[{st['align_min']:.3f},{st['align_mean']:.3f}] "
            f"{st['min_child_mean']:<12.3f} {st['ratio_mean']:.3f}"
        )


if __name__ == "__main__":
    main()
