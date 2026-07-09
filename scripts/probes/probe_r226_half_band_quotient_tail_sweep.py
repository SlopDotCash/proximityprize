#!/usr/bin/env python3
"""#466 R226: exact half-band quotient-tail constant sweep.

R225 reduced the corrected raw half-band MGF route to a quotient-sized tail
certificate

    #{q in Q : theta <= X_q} <= C * |Q| * exp(-theta/2) + K,
    theta > 1/2.

This probe tests the sharp empirical value of `C` needed for exact finite
fields with `p = M*n + 1`.  For a finite spectrum, the worst threshold above
the half-band occurs at one of the observed normalized-square values: between
two adjacent values the survivor count is constant and `exp(theta/2)` is
increasing.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass

import numpy as np


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0:
            return n == q
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError(f"no primitive root found for p={p}")


def subgroup(p: int, n: int) -> np.ndarray:
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    vals = np.empty(n, dtype=np.int64)
    x = 1
    for i in range(n):
        vals[i] = x
        x = (x * step) % p
    return vals


def coset_reps(p: int, n: int) -> np.ndarray:
    g = primitive_root(p)
    m = (p - 1) // n
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for j in range(m):
        reps[j] = x
        x = (x * g) % p
    return reps


def normalized_values_vectorized(p: int, n: int, chunk: int) -> np.ndarray:
    h = subgroup(p, n)
    reps = coset_reps(p, n)
    mags = np.empty(len(reps), dtype=np.float64)
    scale = 2.0 * math.pi / p
    for start in range(0, len(reps), chunk):
        b = reps[start : start + chunk]
        residues = (b[:, None] * h[None, :]) % p
        angles = residues.astype(np.float64) * scale
        real = np.cos(angles).sum(axis=1)
        imag = np.sin(angles).sum(axis=1)
        mags[start : start + len(b)] = real * real + imag * imag
    sigma2 = n * float(mags.sum()) / (p - 1)
    return mags / sigma2


@dataclass(frozen=True)
class TailWitness:
    c_required: float
    theta: float
    count: int
    bound_at_target: float


def exact_required_c(xs: np.ndarray, tau: float, spike_budget: float, target_c: float) -> TailWitness:
    desc = np.sort(xs)[::-1]
    m = len(desc)
    best = TailWitness(0.0, tau, 0, spike_budget + target_c * m * math.exp(-tau / 2.0))
    for idx, x0 in enumerate(desc):
        x = float(x0)
        if x <= tau:
            break
        count = idx + 1
        required = max(0.0, (count - spike_budget) / m) * math.exp(x / 2.0)
        if required > best.c_required:
            bound = target_c * m * math.exp(-x / 2.0) + spike_budget
            best = TailWitness(required, x, count, bound)
    return best


def primes_congruent_one(n: int, min_p: int, max_p: int) -> list[int]:
    p = min_p + ((1 - min_p) % n)
    out: list[int] = []
    while p <= max_p:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[16, 32, 64, 128])
    parser.add_argument("--min-p", type=int, default=3)
    parser.add_argument("--max-p", type=int, default=2_000_000)
    parser.add_argument("--max-cosets", type=int, default=250_000)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--target-c", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--limit-per-n", type=int, default=0, help="0 means no per-n limit")
    args = parser.parse_args()

    rows = []
    skipped = 0
    for n in args.ns:
        tested_for_n = 0
        for p in primes_congruent_one(n, args.min_p, args.max_p):
            m = (p - 1) // n
            if m > args.max_cosets:
                skipped += 1
                continue
            xs = normalized_values_vectorized(p, n, args.chunk)
            witness = exact_required_c(xs, args.tau, args.spike_budget, args.target_c)
            excess = witness.count - witness.bound_at_target
            rows.append((witness.c_required, excess, witness, n, p, m, float(xs.max()), float(np.exp(xs / 4).mean())))
            tested_for_n += 1
            if args.limit_per_n and tested_for_n >= args.limit_per_n:
                break

    rows.sort(reverse=True, key=lambda row: row[0])
    print(
        "R226 half-band quotient-tail exact sweep "
        f"tau={args.tau} C={args.target_c} K={args.spike_budget} "
        f"max_p={args.max_p} max_cosets={args.max_cosets}"
    )
    print("C_req    slack_C   excess    theta    count    M        maxX    mgf1/4  n     p")
    print("-" * 108)
    for c_req, excess, witness, n, p, m, max_x, mgf4 in rows[:40]:
        print(
            f"{c_req:<8.5f} {args.target_c - c_req:<9.5f} {excess:<9.3f} "
            f"{witness.theta:<8.4f} {witness.count:<8d} {m:<8d} "
            f"{max_x:<7.3f} {mgf4:<7.4f} {n:<5d} {p}"
        )
    print("\nsummary")
    print(f"tested={len(rows)} skipped_by_cosets={skipped}")
    if rows:
        worst = rows[0]
        print(
            f"worst_C_required={worst[0]:.8f} slack={args.target_c - worst[0]:.8f} "
            f"n={worst[3]} p={worst[4]} M={worst[5]} theta={worst[2].theta:.8f} "
            f"count={worst[2].count} target_bound={worst[2].bound_at_target:.3f}"
        )
        print(f"target_passes={worst[0] <= args.target_c}")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(130)
