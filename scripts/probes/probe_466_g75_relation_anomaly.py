#!/usr/bin/env python3
"""Probe G75's actual R366 centered relation anomaly.

For G = mu_n in F_p, let
  S_r = sum_{b != 0} |eta_b|^(2r),
  B_r = the characteristic-zero shadow energy,
  A_r = S_r - (p-1) B_r,
  K_r = p Wick_r - (p-1) B_r.
Then A_r is R366's relationAnomaly and A_r <= K_r is the centered target.

The script computes B_r exactly by a return-count recurrence and S_r from the full FFT spectrum.
Default cells include both passing and failing structured examples. Pass --beta4 for the larger
n=64, p=16777729 cell used in the G75 report.
"""

import argparse
import math

import numpy as np
import sympy


def v2(x: int) -> int:
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def subgroup(p: int, n: int) -> list[int]:
    generator = sympy.primitive_root(p)
    zeta = pow(generator, (p - 1) // n, p)
    return [pow(zeta, j, p) for j in range(n)]


def shadow_table(n: int, max_r: int) -> list[int]:
    """Exact B_m(r), length-2r return count on m=n/2 signed coordinates."""
    previous = [0] * (max_r + 1)
    previous[0] = 1
    for _ in range(n // 2):
        current = [0] * (max_r + 1)
        for r in range(max_r + 1):
            current[r] = sum(
                math.comb(2 * r, 2 * k) * math.comb(2 * k, k) * previous[r - k]
                for k in range(r + 1)
            )
        previous = current
    return previous


def spectral_masses(n: int, p: int) -> np.ndarray:
    indicator = np.zeros(p, dtype=np.float64)
    indicator[subgroup(p, n)] = 1.0
    eta = np.fft.fft(indicator)
    return (eta.real * eta.real + eta.imag * eta.imag)[1:]


def log_power_sum(masses: np.ndarray, r: int) -> float:
    positive = masses > 1e-28
    values = r * np.log(masses[positive])
    peak = float(np.max(values))
    return peak + math.log(float(np.sum(np.exp(values - peak))))


def double_factorial(k: int) -> int:
    return math.prod(range(k, 0, -2))


def analyze(n: int, p: int, max_r: int) -> None:
    assert sympy.isprime(p)
    assert (p - 1) % n == 0
    shadow = shadow_table(n, max_r)
    masses = spectral_masses(n, p)
    print(
        f"n={n} p={p} beta={math.log(p, n):.6f} v2={v2(p - 1)} "
        f"M2/n={float(np.max(masses)) / n:.6f}"
    )
    sample_depths = [r for r in (2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40) if r <= max_r]
    for r in sample_depths:
        spectral_to_shadow = math.exp(
            log_power_sum(masses, r) - math.log(p - 1) - math.log(shadow[r])
        )
        wick = double_factorial(2 * r - 1) * n**r
        budget_to_shadow = (p / (p - 1)) * (wick / shadow[r]) - 1.0
        anomaly_to_budget = (spectral_to_shadow - 1.0) / budget_to_shadow
        verdict = "PASS" if anomaly_to_budget <= 1 else "FAIL"
        print(
            f" r={r:2d} S/((p-1)B)={spectral_to_shadow:12.6g} "
            f"K/((p-1)B)={budget_to_shadow:12.6g} "
            f"A/K={anomaly_to_budget:+12.6g} {verdict}"
        )
    print()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta4", action="store_true", help="include the 16.8M-point beta-4 FFT")
    args = parser.parse_args()
    cells = [(32, 1048609), (64, 264961), (64, 355009), (64, 4017089)]
    if args.beta4:
        cells.append((64, 16777729))
    for n, p in cells:
        analyze(n, p, 40)


if __name__ == "__main__":
    main()
