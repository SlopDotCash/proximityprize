#!/usr/bin/env python3
"""#466 R322: full deep-moment census of the 92 dyadically saturated D4 cells.

For every n=32 in-window K-bad prime from R321, evaluate all multiplicative
coset Gauss periods.  Measure K_eff at every depth 1 <= r <= ceil(log p), where

  sum_(b != 0) |eta_b|^(2r) = p K_eff^r (2r-1)!! n^r.

This tests whether primitive-recurrence saturation is compatible with a
uniform exponential Wick allowance throughout the entire logarithmic tower.
"""

from __future__ import annotations

import math
import re
from collections import Counter
from pathlib import Path

import numpy as np
import sympy as sp


ROW = re.compile(r"^(\d+)\s+\d+\s+[0-9.]+\s+\S+\s+\d+\s+\d+\s+(\d+)\s+")


def log_double_factorial_odd(r: int) -> float:
    return math.lgamma(2 * r + 1) - r * math.log(2.0) - math.lgamma(r + 1)


def logsumexp(values: np.ndarray) -> float:
    top = float(np.max(values))
    return top + math.log(float(np.exp(values - top).sum()))


def period_logs(p: int, n: int, chunk: int = 8192) -> np.ndarray:
    index = (p - 1) // n
    primitive = int(sp.primitive_root(p))
    subgroup_generator = pow(primitive, index, p)
    subgroup = np.fromiter(
        (pow(subgroup_generator, j, p) for j in range(n)), dtype=np.int64, count=n
    )
    representatives = np.fromiter(
        (pow(primitive, j, p) for j in range(index)), dtype=np.int64, count=index
    )
    logs = np.empty(index, dtype=np.float64)
    tau = 2.0 * math.pi / p
    for start in range(0, index, chunk):
        reps = representatives[start : start + chunk]
        residues = (reps[:, None] * subgroup[None, :]) % p
        periods = np.exp(1j * tau * residues).sum(axis=1)
        absolute = np.abs(periods)
        logs[start : start + len(reps)] = np.log(
            absolute, where=absolute > 0, out=np.full_like(absolute, -np.inf)
        )
    return logs


def scan(label: str, n: int, primes: list[int]) -> None:
    global_best = (-math.inf, 0, 0)
    log_depth_best = (-math.inf, 0, 0)
    per_depth = Counter()
    for p in primes:
        logs = period_logs(p, n)
        max_depth = math.ceil(math.log(p))
        local_best = (-math.inf, 0)
        for r in range(1, max_depth + 1):
            log_moment = math.log(n) + logsumexp(2.0 * r * logs)
            log_wick = math.log(p) + log_double_factorial_odd(r) + r * math.log(n)
            k_eff = math.exp((log_moment - log_wick) / r)
            if k_eff > local_best[0]:
                local_best = (k_eff, r)
            if k_eff > global_best[0]:
                global_best = (k_eff, p, r)
            if r == max_depth and k_eff > log_depth_best[0]:
                log_depth_best = (k_eff, p, r)
        per_depth[local_best[1]] += 1

    print(f"dataset={label} n={n} cells={len(primes)} depths=1..ceil(log p)")
    print(
        f"  global_max K_eff={global_best[0]:.12f} p={global_best[1]} r={global_best[2]}"
    )
    print(
        f"  log_depth_max K_eff={log_depth_best[0]:.12f} "
        f"p={log_depth_best[1]} r={log_depth_best[2]}"
    )
    print(f"  local_peak_depth_hist={dict(sorted(per_depth.items()))}")


def main() -> int:
    d4_primes = []
    for line in Path("scripts/probes/_out_466_d4_structure.txt").read_text().splitlines():
        match = ROW.match(line)
        if match:
            d4_primes.append(int(match.group(1)))
    n16_primes = []
    bad_row = re.compile(r"p=\s*(\d+).*excess=")
    for line in Path("scripts/probes/_out_466_r305_census_n16.txt").read_text().splitlines():
        match = bad_row.search(line)
        if match:
            n16_primes.append(int(match.group(1)))

    print("# R322 full deep-moment census of saturated depth-4 cells")
    scan("n32_d4_kbad", 32, d4_primes)
    scan("n16_complete_depth3_bad", 16, n16_primes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
