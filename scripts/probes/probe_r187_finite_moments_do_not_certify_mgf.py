#!/usr/bin/env python3
"""#466 R187: finite moments alone cannot certify the MGF(1/4) target.

The R186 target is avg exp(X/4) <= 2.  This probe checks a basic obstruction:
given only finitely many polynomial moment upper bounds, a tiny far-tail spike
can obey all those moment budgets while making the exponential moment huge.
"""

from __future__ import annotations

import math


def gaussian_square_moment(j: int) -> float:
    if j == 0:
        return 1.0
    return math.prod(range(1, 2 * j, 2))


def best_spike(K: int, max_score: float = 2000.0, step: float = 0.1) -> tuple[float, float]:
    best = (0.0, 0.0)
    for i in range(1, int(max_score / step)):
        score = i * step
        mass = min(gaussian_square_moment(j) / (score**j) for j in range(1, K + 1))
        contribution = mass * math.exp(score / 4)
        if contribution > best[0]:
            best = (contribution, score)
    return best


def main() -> None:
    print("K  best_spike_mgf_contribution  score")
    for K in (2, 3, 4, 5, 6, 8, 10, 12, 16, 20):
        value, score = best_spike(K)
        print(f"{K:<2d} {value:.3e} {score:.1f}")


if __name__ == "__main__":
    main()
