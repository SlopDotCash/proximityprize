#!/usr/bin/env python3
"""Exact/numerical falsify-first audit of the #466 AJT13 Jacobi socket.

The proposed all-nontrivial correlation is

  S13 = sum_{a_1,...,a_13 in K*, product != 1} q^-6 J(a_1,...,a_13).

Writing eta_c for the Gauss periods on F_q*/H and m=(q-1)/|H|, character
orthogonality gives the exact positive-moment identity

  S13 = (1/m) sum_c ((m*eta_c+1)/sqrt(q))^14
      = m^13/q^7 sum_c (eta_c+1/m)^14.

For the two highlighted cells the script evaluates this rational number exactly,
without floating-point roots of unity, from zero-sum counts in H.  It also checks
production-exponent analogues and falsifies a naive CRT tensor factorization of
the normalized Gauss phase array.
"""

from __future__ import annotations

import cmath
from fractions import Fraction
from math import comb, pi, sqrt, log


WICK_14 = 135_135  # 13!!
PUBLIC_CONSTANT = 2**18


def is_prime(q: int) -> bool:
    if q < 2:
        return False
    if q % 2 == 0:
        return q == 2
    if q % 3 == 0:
        return q == 3
    d, step = 5, 2
    while d * d <= q:
        if q % d == 0:
            return False
        d += step
        step = 6 - step
    return True


def prime_factors(x: int) -> list[int]:
    ans: list[int] = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            ans.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        ans.append(x)
    return ans


def primitive_root(q: int) -> int:
    factors = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // ell, q) != 1 for ell in factors):
            return g
    raise AssertionError("prime field has no primitive root")


def subgroup(q: int, n: int, m: int) -> list[int]:
    assert q == n * m + 1 and is_prime(q)
    g = primitive_root(q)
    return [pow(g, m * j, q) for j in range(n)]


def exact_socket_ratio(n: int, m: int) -> tuple[int, Fraction, list[int]]:
    """Return q, S13/m^7, and Z_k=#{H^k tuples summing to zero}, k=0..14."""
    q = n * m + 1
    h = subgroup(q, n, m)
    distribution = [0] * q
    distribution[0] = 1
    zero_counts = [1]
    for _k in range(1, 15):
        nxt = [0] * q
        for x in h:
            for total, count in enumerate(distribution):
                if count:
                    nxt[(total + x) % q] += count
        distribution = nxt
        zero_counts.append(distribution[0])

    # M_k=sum over quotient cosets eta_c^k.  Additive orthogonality gives
    # n*M_k=q*Z_k-n^k for k>=1, while M_0=m.
    period_moments = [m]
    for k in range(1, 15):
        dividend = q * zero_counts[k] - n**k
        assert dividend % n == 0
        period_moments.append(dividend // n)

    # Expand sum_c (eta_c+1/m)^14 and multiply by m^13/q^7.
    numerator = sum(
        comb(14, k) * m**k * period_moments[k] for k in range(15)
    )
    socket = Fraction(numerator, m * q**7)
    return q, socket / m**7, zero_counts


def nearest_production_exponent_cell(n: int) -> tuple[int, int]:
    """Find q=n*m+1 prime near m=n^(128/30), the production beta analogue."""
    center = max(2, round(n ** (128 / 30)))
    for delta in range(1_000_000):
        candidates = [center] if delta == 0 else [center - delta, center + delta]
        for m in candidates:
            q = n * m + 1
            if m >= 2 and is_prime(q):
                return m, q
    raise AssertionError("prime search exhausted")


def floating_socket_ratio(n: int, m: int, q: int) -> tuple[float, float]:
    g = primitive_root(q)
    h = [pow(g, m * j, q) for j in range(n)]
    root = cmath.exp(2j * pi / q)
    roots = [root**j for j in range(q)]
    moment, max_a = 0.0, 0.0
    for k in range(m):
        b = pow(g, k, q)
        eta = sum(roots[(b * x) % q] for x in h)
        assert abs(eta.imag) < 2e-8
        a = (m * eta.real + 1) / sqrt(q)
        moment += a**14
        max_a = max(max_a, abs(a))
    socket = moment / m
    return socket / m**7, max_a


def normalized_gauss_phases(q: int, m: int) -> list[complex]:
    g = primitive_root(q)
    discrete_log = [0] * q
    x = 1
    for exponent in range(q - 1):
        discrete_log[x] = exponent
        x = x * g % q
    additive_root = cmath.exp(2j * pi / q)
    additive_values = [additive_root**x for x in range(q)]
    phases: list[complex] = []
    for j in range(m):
        total = sum(
            additive_values[x]
            * cmath.exp(2j * pi * j * (discrete_log[x] % m) / m)
            for x in range(1, q)
        )
        phases.append(total / sqrt(q))
    return phases


def crt_index(u: int, v: int, a: int, b: int) -> int:
    assert a * b > 0
    return next(j for j in range(a * b) if j % a == u and j % b == v)


def max_punctured_crt_minor(q: int, m: int, a: int, b: int) -> tuple[float, list[int], complex]:
    """Rank-one CRT tensors have all these 2x2 minors equal to zero."""
    assert m == a * b
    phases = normalized_gauss_phases(q, m)
    best = (-1.0, [], 0j)
    for u in range(a):
        for up in range(u + 1, a):
            for v in range(b):
                for vp in range(v + 1, b):
                    labels = [
                        crt_index(u, v, a, b),
                        crt_index(u, vp, a, b),
                        crt_index(up, v, a, b),
                        crt_index(up, vp, a, b),
                    ]
                    if 0 in labels:
                        continue
                    minor = phases[labels[0]] * phases[labels[3]] \
                        - phases[labels[1]] * phases[labels[2]]
                    if abs(minor) > best[0]:
                        cross_ratio = phases[labels[0]] * phases[labels[3]] \
                            / (phases[labels[1]] * phases[labels[2]])
                        best = (abs(minor), labels, cross_ratio)
    return best


def main() -> None:
    production_m = 2**128 + 192
    production_factors = [2**6, 7**3, 26407, 279991, 4533259, 462478642316479903]
    assert production_m == __import__("math").prod(production_factors)
    print("AJT13_CENTERED_TENSOR_AUDIT")
    print(f"productionM={production_m}")
    print(f"productionFactors={production_factors}")
    print(f"wick14={WICK_14}; publicConstant={PUBLIC_CONSTANT}; slack={PUBLIC_CONSTANT-WICK_14}")
    print()

    print("EXACT_SMALL_PRIME_CELLS")
    for n, m in [(32, 98), (256, 52)]:
        q, ratio, zero_counts = exact_socket_ratio(n, m)
        print(f"n={n} m={m} q={q} beta={log(q, n):.12f}")
        print(f"S13overM7={ratio.numerator}/{ratio.denominator}")
        print(f"S13overM7Decimal={float(ratio):.12f}")
        print(f"relativeToWick={float(ratio/Fraction(WICK_14)):.12f}")
        print(f"relativeToPublic={float(ratio/Fraction(PUBLIC_CONSTANT)):.12f}")
        print(f"Z14={zero_counts[14]}")
    print("verdict: 13!! and even 2^18 are not universal constants without the production thinness")
    print()

    print("PRODUCTION_BETA_ANALOGUES")
    for n in [2, 4, 8, 16]:
        m, q = nearest_production_exponent_cell(n)
        ratio, max_a = floating_socket_ratio(n, m, q)
        print(
            f"n={n} m={m} q={q} beta={log(q,n):.12f} "
            f"S13overM7={ratio:.12f} relativeToWick={ratio/WICK_14:.12f} maxA={max_a:.9f}"
        )
    print("verdict: m^7 is the observed Wick scaling; its coefficient drifts toward 13!! as n grows")
    print()

    print("CRT_PHASE_TENSOR_MINORS")
    for q, n, m, a, b in [(13, 2, 6, 2, 3), (97, 8, 12, 4, 3), (241, 8, 30, 5, 6), (337, 8, 42, 6, 7)]:
        magnitude, labels, ratio = max_punctured_crt_minor(q, m, a, b)
        print(
            f"q={q} n={n} m={m}={a}x{b} labels={labels} "
            f"maxMinor={magnitude:.12f} crossRatio={ratio.real:.12f}{ratio.imag:+.12f}i"
        )
    exact_q13_ratio = complex(-11 / 13, 4 * sqrt(3) / 13)
    _, _, measured_q13_ratio = max_punctured_crt_minor(13, 6, 2, 3)
    assert abs(measured_q13_ratio - exact_q13_ratio) < 1e-12
    print("q13CrossRatioExact=(-11+4*sqrt(3)*i)/13; minorMagnitude=sqrt(48/13)")
    print("verdict: CRT splits character labels but the additive Gauss phases are not rank-one tensors")


if __name__ == "__main__":
    main()
