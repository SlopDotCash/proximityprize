#!/usr/bin/env python3
r"""DQR-4: adjoining-involution discrepancy and telescoping diagnostics (#466).

At a dyadic step ``G = mu_n < mu_{2n}``, choose ``a`` in ``mu_{2n} \ G``.  If
``q - 1 = n*m`` and a primitive root orders the multiplicative cosets, then ``aG`` is
the *unique involution* ``m/2`` in ``F_q^*/G``.  For the real period vector ``v`` on
that quotient, the normalized signed ledger is

    R(s) = sum_r (v[r] + v[r+s])^14 / sum_r v[r]^14.

The desired per-step Gaussian coefficient is ``R(m/2) <= 2^7``.  The all-twist
mean is computable from the fifteen power sums, while an FFT computes the complete
coset discrepancy distribution and its exact (up to floating evaluation of roots of
unity) L2 diagnostics.

This probe tests three proposed DQR-4 routes:

* orbit/equidistribution: the production point is the quotient involution, not a
  generic orbit point;
* sparse large sieve / Cauchy--Schwarz: report the fraction of all discrepancy L2
  mass carried by the single adjoining point and the pointwise L2 saving;
* telescoping across levels: report each ``log2(R/128)`` increment and its cumulative
  sum, which is an identity rather than a source of cancellation.

The output is a falsifier/diagnostic, not a proof at the 159-bit production prime.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from decimal import Decimal, getcontext

import numpy as np


PRODUCTION_M = (1 << 128) + 192


def prime_factors(n: int) -> list[int]:
    factors: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // ell, p) != 1 for ell in factors):
            return g
    raise ValueError(f"no primitive root found modulo {p}")


def v2(n: int) -> int:
    out = 0
    while n % 2 == 0:
        out += 1
        n //= 2
    return out


def period_coset_vector(p: int, n: int, g: int) -> np.ndarray:
    """Return eta_G(g^r), 0 <= r < (p-1)/n, by one additive FFT."""
    m = (p - 1) // n
    zeta_n = pow(g, m, p)
    indicator = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        indicator[x] = 1.0
        x = (x * zeta_n) % p
    additive_spectrum = np.fft.fft(indicator)
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for r in range(m):
        reps[r] = x
        x = (x * g) % p
    values = additive_spectrum[reps]
    imag_error = float(np.max(np.abs(values.imag)))
    if imag_error > 2e-8:
        raise ArithmeticError(f"period reality error {imag_error:.3e} for p={p}, n={n}")
    return values.real


def circular_cross_correlation(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    """c[s] = sum_r left[r] * right[r+s]."""
    return np.fft.ifft(np.conj(np.fft.fft(left)) * np.fft.fft(right)).real


@dataclass
class LevelResult:
    n: int
    m: int
    ratio: float
    mean: float
    nontrivial_mean: float
    std: float
    zscore: float
    nontrivial_zscore: float
    l2_mass_fraction: float
    nontrivial_l2_mass_fraction: float
    max_ratio: float
    min_ratio: float
    symmetry_error: float
    cross_sign_changes: int


def analyze_level(p: int, n: int, g: int) -> LevelResult:
    m = (p - 1) // n
    if m % 2:
        raise ValueError("the adjoining dyadic coset requires even quotient order")
    v = period_coset_vector(p, n, g)
    denom = float(np.sum(v**14))
    ledger = np.zeros(m, dtype=np.float64)
    production_terms: list[float] = []
    symmetry_error = 0.0
    s0 = m // 2
    for k in range(15):
        corr = circular_cross_correlation(v**k, v ** (14 - k))
        weight = math.comb(14, k)
        ledger += weight * corr
        production_terms.append(weight * float(corr[s0]) / denom)
        symmetry_error = max(symmetry_error, abs(float(corr[s0] -
                                                       circular_cross_correlation(
                                                           v ** (14 - k), v**k
                                                       )[s0])))
    ratios = ledger / denom
    ratio = float(ratios[s0])
    mean = float(np.mean(ratios))
    deviations = ratios - mean
    std = float(np.sqrt(np.mean(deviations**2)))
    l2 = float(np.sum(deviations**2))
    l2_mass_fraction = 0.0 if l2 == 0.0 else float(deviations[s0] ** 2 / l2)
    zscore = 0.0 if std == 0.0 else float(deviations[s0] / std)
    nontrivial_ratios = ratios[1:]
    nontrivial_mean = float(np.mean(nontrivial_ratios))
    nontrivial_deviations = nontrivial_ratios - nontrivial_mean
    nontrivial_std = float(np.sqrt(np.mean(nontrivial_deviations**2)))
    nontrivial_l2 = float(np.sum(nontrivial_deviations**2))
    production_nontrivial_deviation = ratio - nontrivial_mean
    nontrivial_zscore = (0.0 if nontrivial_std == 0.0 else
                         production_nontrivial_deviation / nontrivial_std)
    nontrivial_l2_mass_fraction = (0.0 if nontrivial_l2 == 0.0 else
                                   production_nontrivial_deviation**2 / nontrivial_l2)
    nontrivial = production_terms[1:14]
    signs = [1 if x > 1e-10 else -1 if x < -1e-10 else 0 for x in nontrivial]
    cross_sign_changes = sum(a != 0 and b != 0 and a != b for a, b in zip(signs, signs[1:]))
    return LevelResult(
        n=n,
        m=m,
        ratio=ratio,
        mean=mean,
        nontrivial_mean=nontrivial_mean,
        std=std,
        zscore=zscore,
        nontrivial_zscore=nontrivial_zscore,
        l2_mass_fraction=l2_mass_fraction,
        nontrivial_l2_mass_fraction=nontrivial_l2_mass_fraction,
        max_ratio=float(np.max(ratios)),
        min_ratio=float(np.min(ratios)),
        symmetry_error=symmetry_error / max(1.0, denom),
        cross_sign_changes=cross_sign_changes,
    )


def run_prime(p: int, max_n: int | None) -> None:
    g = primitive_root(p)
    max_power = v2(p - 1) - 1
    if max_n is not None:
        max_power = min(max_power, int(math.log2(max_n)))
    print(f"\np={p} primitive_root={g} v2(p-1)={v2(p-1)}")
    print(" n       m       R(involution)  Rmean       R/128   z(all) z(disj) "
          "point/L2(disj) range[min,max]          signchg")
    cumulative = 0.0
    results: list[LevelResult] = []
    for exponent in range(1, max_power + 1):
        n = 1 << exponent
        result = analyze_level(p, n, g)
        results.append(result)
        increment = math.log2(result.ratio / 128.0) if result.ratio > 0 else float("-inf")
        cumulative += increment
        print(
            f"{result.n:6d} {result.m:7d} {result.ratio:14.6f} "
            f"{result.mean:10.4f} {result.ratio / 128:8.4f} "
            f"{result.zscore:7.3f} {result.nontrivial_zscore:7.3f} "
            f"{result.nontrivial_l2_mass_fraction:14.6f} "
            f"[{result.min_ratio:8.2f},{result.max_ratio:8.2f}] "
            f"{result.cross_sign_changes:3d}  dlog2={increment:+8.4f} "
            f"tel={cumulative:+8.4f}"
        )
        if result.symmetry_error > 1e-7:
            raise ArithmeticError(
                f"T_kj=T_jk failed at the quotient involution: {result.symmetry_error:.3e}"
            )
    if not results:
        return
    expanding = sum(r.ratio > 128.0 for r in results)
    coherent = sum(abs(r.zscore) > 2.0 for r in results)
    print(
        f"summary levels={len(results)} R>128={expanding} |z|>2={coherent} "
        "max_point_L2_fraction(disjoint)="
        f"{max(r.nontrivial_l2_mass_fraction for r in results):.6f}"
    )


def abstract_mean_symmetry_falsifier(m: int) -> None:
    """A mean-zero inversion-symmetric field concentrated at the unique involution."""
    if m < 4 or m % 2:
        raise ValueError("m must be even and at least four")
    # d(m/2)=m-1 and d(s)=-1 otherwise.  The field is inversion-symmetric,
    # sum d=0, sum d^2=m(m-1), and the fixed-point mass fraction is (m-1)/m.
    getcontext().prec = 60
    mass_fraction = Decimal(m - 1) / Decimal(m)
    deficit = Decimal(1) / Decimal(m)
    print(
        f"\nabstract falsifier m={m}: mean=0 inversion_error=0 involution={m-1} "
        f"point/L2={mass_fraction} deficit={deficit:.6E}\n"
        "  (at production this is 1-O(2^-128), so mean+symmetry+CS give no dilution)"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", nargs="+", type=int, default=[257, 12289, 65537])
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--falsifier-m", type=int, default=PRODUCTION_M)
    args = parser.parse_args()
    abstract_mean_symmetry_falsifier(args.falsifier_m)
    for p in args.primes:
        run_prime(p, args.max_n)


if __name__ == "__main__":
    main()
