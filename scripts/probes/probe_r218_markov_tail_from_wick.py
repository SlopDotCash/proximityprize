#!/usr/bin/env python3
"""#466 R218: can Wick/exponential moments certify the half-rate tail?

R218 formalizes Markov moment certificates for the R216 survival grid.  This
probe tests the optimistic model

    E[X^r] <= A * r! / c^r

for the normalized-square spectrum and optimizes the Markov order at each
threshold:

    P[X >= T] <= min_r A * r! / (c*T)^r.

It compares that envelope to the R217 target

    0.6 * exp(-T/2) + K/M.
"""

from __future__ import annotations

import argparse
import math


def log_factorials(max_r: int) -> list[float]:
    out = [0.0]
    acc = 0.0
    for r in range(1, max_r + 1):
        acc += math.log(r)
        out.append(acc)
    return out


def best_markov(T: float, max_r: int, A: float, c: float, logs: list[float]) -> tuple[float, int]:
    if T <= 0:
        return 1.0, 0
    best_log = 0.0
    best_r = 0
    log_cT = math.log(c * T)
    for r in range(1, max_r + 1):
        value_log = math.log(A) + logs[r] - r * log_cT
        if r == 1 or value_log < best_log:
            best_log = value_log
            best_r = r
    return min(1.0, math.exp(best_log)), best_r


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--max-t", type=float, default=64.0)
    parser.add_argument("--max-r", type=int, default=256)
    parser.add_argument("--A", type=float, default=1.0)
    parser.add_argument("--c", type=float, default=1.0)
    parser.add_argument("--bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--M", type=float, default=2.0**128)
    args = parser.parse_args()

    logs = log_factorials(args.max_r)
    rows = []
    j = 1
    while j * args.step <= args.max_t + 1e-12:
        T = j * args.step
        markov, r = best_markov(T, args.max_r, args.A, args.c, logs)
        target = args.bulk * math.exp(-T / 2) + args.spike_budget / args.M
        ratio = markov / target if target > 0 else math.inf
        rows.append((ratio, T, markov, target, r))
        j += 1

    rows.sort(reverse=True)
    print(
        f"R218 Markov-from-moments A={args.A} c={args.c} max_r={args.max_r} "
        f"target={args.bulk}*exp(-T/2)+{args.spike_budget}/M M={args.M:g}"
    )
    print("worst ratio rows")
    print("ratio      T      markov      target      r")
    print("-" * 64)
    for ratio, T, markov, target, r in rows[:20]:
        print(f"{ratio:<10.4g} {T:<6.2f} {markov:<11.4g} {target:<11.4g} {r}")
    print("\nsummary")
    worst = rows[0]
    print(
        f"worst_ratio={worst[0]:.6g} T={worst[1]:.3f} "
        f"markov={worst[2]:.6g} target={worst[3]:.6g} r={worst[4]}"
    )
    print(f"certifies_all={worst[0] <= 1.0}")


if __name__ == "__main__":
    main()
