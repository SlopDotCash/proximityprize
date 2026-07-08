#!/usr/bin/env python3
"""#466 R170: closed-form survival ceilings for the R169 grid certificate.

R169 showed exact dyadic spectra satisfy the finite-grid MGF certificate with
large slack.  This probe searches for simple uniform count laws

    N(T) <= C * M * exp(-a T)

that both hold on the stress grid and imply the R168 MGF budget through the
same h=0.5 staircase.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    is_prime,
    subgroup,
)


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def grid(step: float, tmax: float) -> list[float]:
    out = []
    k = 0
    while k * step <= tmax + 1e-12:
        out.append(k * step)
        k += 1
    return out


def counts(xs: list[float], ts: list[float]) -> list[int]:
    return [sum(1 for x in xs if x >= t) for t in ts]


def staircase_budget_constant(step: float, tmax: float, a: float, rate: float = 1 / 8) -> float:
    ts = grid(step, tmax)
    total = math.exp(rate * ts[0])
    for j in range(len(ts) - 1):
        delta = math.exp(rate * ts[j + 1]) - math.exp(rate * ts[j])
        total += delta * math.exp(-a * ts[j])
    return total


def main() -> None:
    step = 0.5
    tmax = 40.0
    spectra = []
    for n in (8, 16, 32, 64, 128):
        count = 8 if n <= 64 else 3
        for start in (max(257, n**2), n**3, n**4):
            for p in next_primes_congruent_one(n, start, count):
                if p > 350_000_000:
                    continue
                xs = normalized_values(p, n)
                spectra.append((n, p, xs))

    ts = [t for t in grid(step, 32.0) if t >= 1.0]
    candidates = [(1.0, 0.25), (0.75, 0.25), (0.6, 0.25), (1.0, 1 / 3), (0.75, 1 / 3), (1.0, 0.4)]
    print("C      a       max_tail_ratio  budget_const  verdict")
    print("-" * 68)
    for C, a in candidates:
        worst = (0.0, None)
        for n, p, xs in spectra:
            m = len(xs)
            ns = counts(xs, ts)
            for t, count in zip(ts, ns, strict=True):
                denom = C * m * math.exp(-a * t)
                ratio = count / denom if denom else float("inf")
                if ratio > worst[0]:
                    worst = (ratio, (n, p, t, count, m))
        budget = C * staircase_budget_constant(step, tmax, a)
        verdict = "OK" if worst[0] <= 1 + 1e-9 and budget <= 2 + 1e-9 else "FAIL"
        print(f"{C:<6.3g} {a:<7.4g} {worst[0]:<15.6f} {budget:<13.6f} {verdict}")
        if worst[1] is not None:
            n, p, t, count, m = worst[1]
            print(f"  worst n={n} p={p} T={t:g} count={count}/{m}")

    print(f"\nstress spectra={len(spectra)} thresholds={len(ts)}")


if __name__ == "__main__":
    main()
