#!/usr/bin/env python3
"""R378: Fourier flatness of multiplicative derivatives of Gauss-sum phases.

For H=mu_n in F_p, form the m=(p-1)/n Gaussian periods on multiplicative
cosets. Their length-m DFT is, up to normalization and the trivial character,
the Gauss-sum phase sequence u. For selected shifts h this probe reports the
Fourier norm of D_h u(j)=u(j+h) conjugate(u(j)), and then iterates derivatives.

The output is discovery evidence only. Constant-size derivative Fourier norms
do not by themselves prove the required PAPR estimate.
"""

import argparse
import math

import numpy as np


def prime_factors(n: int) -> list[int]:
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    return next(
        g for g in range(2, p)
        if all(pow(g, (p - 1) // ell, p) != 1 for ell in factors)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("p", type=int)
    parser.add_argument("--depth", type=int, default=8)
    args = parser.parse_args()
    n, p = args.n, args.p
    if (p - 1) % n:
        raise SystemExit("n must divide p-1")

    root = primitive_root(p)
    subgroup_generator = pow(root, (p - 1) // n, p)
    subgroup = []
    value = 1
    for _ in range(n):
        subgroup.append(value)
        value = value * subgroup_generator % p

    indicator = np.zeros(p, dtype=np.float64)
    indicator[subgroup] = 1
    additive_periods = np.fft.fft(indicator)

    m = (p - 1) // n
    representatives = np.empty(m, dtype=np.int64)
    value = 1
    for j in range(m):
        representatives[j] = value
        value = value * root % p
    periods = additive_periods[representatives]
    gauss_phases = np.fft.fft(periods) / math.sqrt(p)

    papr = float(np.max(np.abs(periods)) / math.sqrt(n))
    print(f"n={n} p={p} m={m} periodPAPR={papr:.12g}")
    print(
        "nontrivial phase magnitudes",
        float(np.min(np.abs(gauss_phases[1:]))),
        float(np.max(np.abs(gauss_phases[1:]))),
    )

    for shift in (1, 2, 3, 5, 7, 11, max(1, m // 3)):
        derivative = np.roll(gauss_phases, -shift) * np.conj(gauss_phases)
        transform = np.fft.fft(derivative)
        print(
            f"shift={shift:8d}",
            f"derivativeFourierMax/sqrt(m)={np.max(np.abs(transform))/math.sqrt(m):.12g}",
            f"correlation/sqrt(m)={abs(transform[0])/math.sqrt(m):.12g}",
        )

    derivative = gauss_phases.copy()
    for depth in range(1, args.depth + 1):
        shift = 1 << (depth - 1)
        derivative = np.roll(derivative, -shift) * np.conj(derivative)
        transform = np.fft.fft(derivative)
        print(
            f"depth={depth:2d}",
            f"shift={shift:8d}",
            f"fourierMax/sqrt(m)={np.max(np.abs(transform))/math.sqrt(m):.12g}",
        )


if __name__ == "__main__":
    main()
