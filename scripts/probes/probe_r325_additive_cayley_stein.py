#!/usr/bin/env python3
"""Test the exact-regression additive Cayley exchangeable pair for Gauss periods."""

from __future__ import annotations

import argparse
import json

import numpy as np


DEFAULT_CASES = [(16, 65537), (32, 1048609), (32, 1439393)]


def subgroup(p: int, n: int) -> np.ndarray:
    assert (p - 1) % n == 0
    # Find a primitive root by factoring p - 1 (the probe cases are modest).
    factors = []
    q = p - 1
    d = 2
    while d * d <= q:
        if q % d == 0:
            factors.append(d)
            while q % d == 0:
                q //= d
        d += 1
    if q > 1:
        factors.append(q)
    g = next(a for a in range(2, p) if all(pow(a, (p - 1) // r, p) != 1 for r in factors))
    h = pow(g, (p - 1) // n, p)
    return np.array([pow(h, j, p) for j in range(n)], dtype=np.int64)


def analyze(n: int, p: int) -> dict[str, float | int]:
    G = subgroup(p, n)
    indicator = np.zeros(p, dtype=np.float64)
    indicator[G] = 1.0
    X = np.fft.fft(indicator).real
    c = X[1] / n
    lam = 1.0 - c

    PX = np.zeros(p)
    jump2 = np.zeros(p)
    for t in G:
        shifted = np.roll(X, -int(t))
        PX += shifted
        jump2 += (shifted - X) ** 2
    PX /= n
    jump2 /= n
    V = jump2 / (2.0 * lam)

    nonzero = np.arange(1, p)
    worst = int(nonzero[np.argmax(V[1:])])
    hit_dc = np.isin((-nonzero) % p, G)
    boundary_max = float(np.max(V[nonzero[hit_dc]]))
    interior_max = float(np.max(V[nonzero[~hit_dc]]))
    return {
        "n": n,
        "p": p,
        "eta1": float(X[1]),
        "lambda": float(lam),
        "regression_error": float(np.max(np.abs(PX - c * X))),
        "max_abs_period_nonzero": float(np.max(np.abs(X[1:]))),
        "max_V_over_n_nonzero": float(V[worst] / n),
        "worst_b": worst,
        "worst_X": float(X[worst]),
        "boundary_max_V_over_n": boundary_max / n,
        "interior_max_V_over_n": interior_max / n,
        "dc_V_over_n": float(V[0] / n),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", nargs=2, action="append", metavar=("N", "P"), type=int)
    args = parser.parse_args()
    cases = [tuple(x) for x in args.case] if args.case else DEFAULT_CASES
    print(json.dumps([analyze(n, p) for n, p in cases], indent=2))


if __name__ == "__main__":
    main()
