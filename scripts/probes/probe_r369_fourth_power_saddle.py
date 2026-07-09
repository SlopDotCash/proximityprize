#!/usr/bin/env python3
"""R369: test the fourth-power saddle-moment hypothesis for a dyadic subgroup.

For H = mu_n in F_p and r >= 2, this prints

  (E_r(H) - n^(2r)/p) / ((2r-1)!! n^r),

the normalized DC-subtracted moment.  A value at most one is exactly the
numerical form of DCEnergyBound.  The default final depth is ceil(log p), the
single saddle rung consumed by DCOptimized; --all continues beyond it.

This is a floating-point falsification probe, not a proof certificate.  Depth
3 can be checked independently by the exact grouped-shadow probes R305/R368.
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


def odd_double_factorial(r: int) -> int:
    answer = 1
    for value in range(1, 2 * r, 2):
        answer *= value
    return answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("p", type=int)
    parser.add_argument("--all", action="store_true", help="continue to twice the saddle depth")
    args = parser.parse_args()

    n, p = args.n, args.p
    if (p - 1) % n:
        raise SystemExit("n must divide p-1")
    saddle = math.ceil(math.log(p))
    last = 2 * saddle if args.all else saddle

    generator = pow(primitive_root(p), (p - 1) // n, p)
    subgroup = []
    value = 1
    for _ in range(n):
        subgroup.append(value)
        value = value * generator % p
    if value != 1 or len(set(subgroup)) != n:
        raise SystemExit("failed to construct a subgroup of exact order n")

    indicator = np.zeros(p, dtype=np.float64)
    indicator[subgroup] = 1
    periods = np.fft.fft(indicator)
    normalized_sq = np.abs(periods) ** 2 / n

    print(f"n={n} p={p} n^4={n**4} saddle={saddle}")
    for r in range(2, last + 1):
        normalized_sum = float(np.sum(normalized_sq ** r, dtype=np.float64))
        ratio = ((normalized_sum - n**r) / p) / odd_double_factorial(r)
        verdict = "PASS" if ratio <= 1 + 1e-7 else "FAIL"
        print(f"r={r:3d} ratio={ratio:.12g} {verdict}")


if __name__ == "__main__":
    main()
