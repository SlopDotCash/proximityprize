#!/usr/bin/env python3
"""#466 R229: cutoff scan for the one-band/twelve-spike MGF route.

R226 found a quotient tail shape that survives broad exact sweeps:

    N_q(theta) <= C * M * exp(-theta/2) + K,  theta > tau,

with `tau = 1`, `C = 3/5`, and `K = 12`.  This probe asks the next question:
for which quotient indices `M = (p - 1) / n` does the resulting weighted
staircase certificate actually prove the quarter-MGF target `<= 2`?

It reports two independent quantities:

* `mgf1/4`: the exact empirical normalized quotient MGF.
* `env_budget`: the closed staircase budget obtained from exact low-band
  payment and the above exponential tail envelope.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)


@dataclass(frozen=True)
class CaseResult:
    env_budget: float
    mgf4: float
    max_x: float
    n: int
    p: int
    m: int
    label: str


def staircase_deltas(step: float, cutoff: float, rate: float) -> list[tuple[float, float]]:
    if step <= 0:
        raise ValueError("step must be positive")
    thetas = [j * step for j in range(math.ceil(cutoff / step) + 1)]
    out: list[tuple[float, float]] = []
    prev = 0.0
    for theta in thetas:
        cap = min(theta + step, cutoff + step)
        cumulative = math.exp(rate * cap)
        out.append((theta, cumulative - prev))
        prev = cumulative
    return out


def envelope_budget(
    m: int,
    step: float,
    cutoff: float,
    tau: float,
    c_bulk: float,
    spike_budget: float,
    rate: float,
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if theta <= tau:
            bound_per_quotient = 1.0
        else:
            bound_per_quotient = c_bulk * math.exp(-theta / 2.0) + spike_budget / m
        total += delta * bound_per_quotient
    return total


def medium_cases(max_a: int, max_index: int, min_index: int) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    for a in range(3, max_a + 1):
        n = 2**a
        for m in range(max(2, min_index), max_index + 1):
            p = m * n + 1
            if is_prime(p):
                out.append((n, p, f"medium-a={a}-M={m}"))
    return out


def window_cases(ns: list[int], min_p: int, max_p: int, limit_per_n: int) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    for n in ns:
        found = 0
        p = min_p + ((1 - min_p) % n)
        while p <= max_p:
            if is_prime(p):
                out.append((n, p, f"window-M={(p - 1) // n}"))
                found += 1
                if limit_per_n and found >= limit_per_n:
                    break
            p += n
    return out


def evaluate_case(
    n: int,
    p: int,
    label: str,
    chunk: int,
    step: float,
    tau: float,
    c_bulk: float,
    spike_budget: float,
    rate: float,
) -> CaseResult:
    xs = normalized_values_vectorized(p, n, chunk)
    max_x = float(xs.max())
    m = len(xs)
    return CaseResult(
        env_budget=envelope_budget(m, step, max_x, tau, c_bulk, spike_budget, rate),
        mgf4=float(np.exp(xs * rate).mean()),
        max_x=max_x,
        n=n,
        p=p,
        m=m,
        label=label,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["medium", "window", "mixed"], default="mixed")
    parser.add_argument("--medium-max-a", type=int, default=11)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=2)
    parser.add_argument("--ns", type=int, nargs="+", default=[16, 32, 64, 128, 256])
    parser.add_argument("--min-p", type=int, default=65537)
    parser.add_argument("--max-p", type=int, default=5_000_000)
    parser.add_argument("--limit-per-n", type=int, default=80)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--step", type=float, default=0.125)
    parser.add_argument("--tau", type=float, default=1.0)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=12.0)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--top", type=int, default=40)
    parser.add_argument("--sort", choices=["env", "mgf", "maxx", "m"], default="env")
    parser.add_argument("--fail-only", choices=["none", "env", "mgf", "either"], default="none")
    args = parser.parse_args()

    cases: list[tuple[int, int, str]] = []
    if args.mode in ("medium", "mixed"):
        cases.extend(medium_cases(args.medium_max_a, args.medium_max_index, args.min_index))
    if args.mode in ("window", "mixed"):
        cases.extend(window_cases(args.ns, args.min_p, args.max_p, args.limit_per_n))
    cases = sorted(set(cases), key=lambda row: (row[1], row[0], row[2]))

    all_rows = [
        evaluate_case(
            n,
            p,
            label,
            args.chunk,
            args.step,
            args.tau,
            args.c_bulk,
            args.spike_budget,
            args.rate,
        )
        for n, p, label in cases
    ]
    env_fail = [r for r in all_rows if r.env_budget > 2.0 + 1e-9]
    mgf_fail = [r for r in all_rows if r.mgf4 > 2.0 + 1e-9]
    display_rows = list(all_rows)
    if args.fail_only == "env":
        display_rows = env_fail
    elif args.fail_only == "mgf":
        display_rows = mgf_fail
    elif args.fail_only == "either":
        display_rows = [r for r in all_rows if r.env_budget > 2.0 + 1e-9 or r.mgf4 > 2.0 + 1e-9]
    if args.sort == "env":
        display_rows.sort(key=lambda r: (r.env_budget, r.mgf4), reverse=True)
    elif args.sort == "mgf":
        display_rows.sort(key=lambda r: (r.mgf4, r.env_budget), reverse=True)
    elif args.sort == "maxx":
        display_rows.sort(key=lambda r: (r.max_x, r.mgf4), reverse=True)
    else:
        display_rows.sort(key=lambda r: (r.m, r.env_budget), reverse=True)

    print(
        "R229 one-band MGF cutoff scan "
        f"mode={args.mode} tau={args.tau} C={args.c_bulk} K={args.spike_budget} "
        f"step={args.step} displayed={len(display_rows)} total={len(cases)} "
        f"sort={args.sort} fail_only={args.fail_only}"
    )
    print("env      env_slack mgf1/4   mgf_slack maxX    M        n     p          label")
    print("-" * 116)
    for r in display_rows[: args.top]:
        print(
            f"{r.env_budget:<8.4f} {2-r.env_budget:<9.4f} {r.mgf4:<8.4f} "
            f"{2-r.mgf4:<9.4f} {r.max_x:<7.3f} {r.m:<8d} {r.n:<5d} {r.p:<10d} {r.label}"
        )

    print("\nsummary")
    print(f"env_failures={len(env_fail)} mgf_failures={len(mgf_fail)}")
    if all_rows:
        worst_env = max(all_rows, key=lambda r: r.env_budget)
        print(
            f"worst_env={worst_env.env_budget:.6f} slack={2-worst_env.env_budget:.6f} "
            f"n={worst_env.n} p={worst_env.p} M={worst_env.m} maxX={worst_env.max_x:.6f}"
        )
        worst_mgf = max(all_rows, key=lambda r: r.mgf4)
        print(
            f"worst_mgf={worst_mgf.mgf4:.6f} slack={2-worst_mgf.mgf4:.6f} "
            f"n={worst_mgf.n} p={worst_mgf.p} M={worst_mgf.m} maxX={worst_mgf.max_x:.6f}"
        )
        passing_ms = [r.m for r in all_rows if r.env_budget <= 2.0 + 1e-9 and r.mgf4 <= 2.0 + 1e-9]
        failing_ms = [r.m for r in all_rows if r.env_budget > 2.0 + 1e-9 or r.mgf4 > 2.0 + 1e-9]
        env_failing_ms = [r.m for r in env_fail]
        mgf_failing_ms = [r.m for r in mgf_fail]
        if passing_ms:
            print(f"min_passing_M={min(passing_ms)}")
        if failing_ms:
            print(f"max_failing_M={max(failing_ms)}")
        if env_failing_ms:
            print(f"max_env_failing_M={max(env_failing_ms)}")
        if mgf_failing_ms:
            print(f"max_mgf_failing_M={max(mgf_failing_ms)}")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(130)
