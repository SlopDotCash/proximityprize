#!/usr/bin/env python3
"""Exact no-go probe for the proposed Möbius-Mann connected-packet expansion.

For a multiplicative subgroup H of F_p, let M_m count ordered m-words in H
whose sum is zero. Define the classical connected coefficients K_m by

    M_m = sum_{pi partition [m]} product_{B in pi} K_|B|.

Equivalently, K is obtained by Möbius inversion on the set-partition lattice.
The probe checks two obstructions:

1. K_m is signed and is not the number of primitive zero-sum packets. At
   length four, primitive4 = M_4 - (3 n^2 - 3 n), whereas K_4 = M_4 - 3 n^2.
2. Replacing every positive-length M_m by the random finite-field main term
   n^m/q makes K_m/n^m the Bernoulli(1/q) cumulant. At production signed
   length 220 and q=2^160, its magnitude is about 2^59 times the DC main
   term, so uncentered Möbius inversion amplifies rather than removes DC.

Pure Python, exact integer/rational arithmetic, no third-party dependencies.
"""

from fractions import Fraction
from math import comb, log2


def prime_factors(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // ell, p) != 1 for ell in factors):
            return g
    raise ValueError(f"no primitive root found modulo {p}")


def subgroup(n: int, p: int) -> list[int]:
    assert (p - 1) % n == 0
    zeta = pow(primitive_root(p), (p - 1) // n, p)
    values = [pow(zeta, j, p) for j in range(n)]
    assert len(set(values)) == n
    return values


def zero_sum_moments(n: int, p: int, limit: int) -> list[int]:
    values = subgroup(n, p)
    distribution = [0] * p
    distribution[0] = 1
    moments = [1]
    for _ in range(limit):
        next_distribution = [0] * p
        for residue, count in enumerate(distribution):
            if count:
                for x in values:
                    next_distribution[(residue + x) % p] += count
        distribution = next_distribution
        moments.append(distribution[0])
    return moments


def connected_coefficients(moments):
    """Distinguished-block recurrence for the partition moment-cumulant law."""
    limit = len(moments) - 1
    connected = [moments[0] * 0 for _ in range(limit + 1)]
    for m in range(1, limit + 1):
        connected[m] = moments[m] - sum(
            comb(m - 1, k - 1) * connected[k] * moments[m - k]
            for k in range(1, m)
        )
    for m in range(1, limit + 1):
        reconstructed = sum(
            comb(m - 1, k - 1) * connected[k] * moments[m - k]
            for k in range(1, m + 1)
        )
        assert reconstructed == moments[m]
    return connected


def odd_double_factorial(m: int) -> int:
    out = 1
    for x in range(1, m + 1, 2):
        out *= x
    return out


def log2_fraction(value: Fraction) -> float:
    return log2(abs(value.numerator)) - log2(value.denominator)


def finite_cells() -> None:
    print("finite exact cells")
    print("n p M3 primitive4 K4 K6 K8 K10 K12 K14")
    cells = [(8, 17), (8, 41), (8, 257), (16, 97), (16, 193),
             (16, 257), (32, 193), (32, 257), (32, 577)]
    for n, p in cells:
        moments = zero_sum_moments(n, p, 14)
        connected = connected_coefficients(moments)
        lawful4 = 3 * n * n - 3 * n
        primitive4 = moments[4] - lawful4
        assert primitive4 >= 0
        assert connected[4] == primitive4 - 3 * n
        row = [n, p, moments[3], primitive4]
        row.extend(connected[m] for m in (4, 6, 8, 10, 12, 14))
        print(*row)

    # This cell has no primitive four-packet, yet its Möbius coefficient is negative.
    moments = zero_sum_moments(8, 257, 4)
    connected = connected_coefficients(moments)
    assert moments[4] - (3 * 8 * 8 - 3 * 8) == 0
    assert connected[4] == -24
    print("witness n=8 p=257: primitive4=0 but K4=-24")


def production_random_bulk() -> None:
    q = 2**160
    n = 2**30
    limit = 220
    # Normalize out n^m. The random moments are b_0=1 and b_m=1/q for m>0.
    moments = [Fraction(1)] + [Fraction(1, q) for _ in range(limit)]
    connected = connected_coefficients(moments)
    kappa = connected[limit]
    relative_to_dc = abs(kappa) * q
    log_kappa_over_dc = log2_fraction(relative_to_dc)
    r = limit // 2
    log_dc_over_wick = (
        limit * 30
        - 160
        - log2(odd_double_factorial(limit - 1))
        - r * 30
    )
    print("production random-main model")
    print(f"sign(K220)={'negative' if kappa < 0 else 'positive'}")
    print(f"log2(|K220|/DC)={log_kappa_over_dc:.6f}")
    print(f"log2(DC/Wick)={log_dc_over_wick:.6f}")
    print(f"log2(|K220|/Wick)={log_kappa_over_dc + log_dc_over_wick:.6f}")
    assert kappa < 0
    assert 58.999 < log_kappa_over_dc < 59.001
    assert 2501 < log_kappa_over_dc + log_dc_over_wick < 2502


if __name__ == "__main__":
    finite_cells()
    production_random_bulk()
