#!/usr/bin/env python3
"""#466 R323: is dyadic recurrence saturation diagnostic at depth three?

Classify the dominant relation orbit for every prime in the complete n=32
depth-3 bad-prime census.  Record whether |Res(x^16+1,f)|/p is a power of two,
then compare dyadically saturated and odd-cofactor cells using the actual
DC-subtracted real-Wick ratio.
"""

from __future__ import annotations

import math
import re
from collections import Counter, defaultdict
from pathlib import Path

import sympy as sp

from probe_r307_binomial_norm_depth3 import order_n_element
from probe_r320_collision_orbit_coherence import orbit_key, shadow_histogram


ROW = re.compile(r"p=\s*(\d+).*excess=(\d+)")


def main() -> int:
    n, r, m = 32, 3, 16
    char0 = 15 * n**3 - 45 * n**2 + 40 * n
    wick = 15 * n**3
    hist = shadow_histogram(n, r)
    rows = []
    for line in Path("scripts/probes/_out_466_r305_census_n32.txt").read_text().splitlines():
        match = ROW.search(line)
        if match:
            rows.append(tuple(map(int, match.groups())))

    x = sp.symbols("x")
    cyclotomic = x**m + 1
    classes = defaultdict(list)
    by_quotient = defaultdict(list)
    quotient_hist = Counter()
    failures = []
    for p, expected_mass in rows:
        g = order_n_element(p, n)
        powers = [pow(g, j, p) for j in range(m)]
        fibers = defaultdict(list)
        for vec, weight in hist.items():
            fibers[sum(a * b for a, b in zip(vec, powers)) % p].append((vec, weight))

        orbit_mass = Counter()
        for fiber in fibers.values():
            for i, (left, wl) in enumerate(fiber):
                for right, wr in fiber[i + 1 :]:
                    diff = tuple(a - b for a, b in zip(left, right))
                    orbit_mass[orbit_key(diff, n)] += 2 * wl * wr
        total = sum(orbit_mass.values())
        assert total == expected_mass
        key, top_mass = orbit_mass.most_common(1)[0]
        poly = sum(coeff * x**j for j, coeff in enumerate(key))
        resultant = abs(int(sp.resultant(cyclotomic, poly, x)))
        quotient, remainder = divmod(resultant, p)
        if remainder:
            failures.append((p, resultant, remainder))
        dyadic = remainder == 0 and quotient > 0 and quotient & (quotient - 1) == 0
        odd_part = quotient
        while odd_part and odd_part % 2 == 0:
            odd_part //= 2
        dc_wick_ratio = (char0 + total - n ** (2 * r) / p) / wick
        beta = math.log(p) / math.log(n)
        classes[dyadic].append((dc_wick_ratio, p, beta, top_mass / total, quotient, odd_part))
        by_quotient[quotient].append(
            (dc_wick_ratio, p, beta, top_mass / total, quotient, odd_part)
        )
        if quotient <= 64:
            quotient_hist[quotient] += 1

    print("# R323 complete depth-3 saturation diagnostic")
    print(
        f"n={n} r={r} cells={len(rows)} shadow_keys={len(hist)} "
        f"resultant_divisibility_failures={len(failures)}"
    )
    print(f"small_quotient_hist={dict(sorted(quotient_hist.items()))}")
    for dyadic in (True, False):
        cells = classes[dyadic]
        worst = max(cells)
        high_beta = [cell for cell in cells if cell[2] > 4.0]
        super_wick = [cell for cell in cells if cell[0] > 1.0]
        print(
            f"class={'dyadic' if dyadic else 'odd_cofactor'} count={len(cells)} "
            f"high_beta={len(high_beta)} super_wick={len(super_wick)} "
            f"worst_ratio={worst[0]:.12f} worst_p={worst[1]} "
            f"worst_beta={worst[2]:.6f} top_share={worst[3]:.9f} "
            f"quotient={worst[4]} odd_part={worst[5]}"
        )
    high_beta_super = sorted(
        cell for cells in classes.values() for cell in cells if cell[2] > 4.0 and cell[0] > 1.0
    )
    for cell in high_beta_super:
        print(
            f"high_beta_super_wick p={cell[1]} ratio={cell[0]:.12f} beta={cell[2]:.6f} "
            f"top_share={cell[3]:.9f} quotient={cell[4]} odd_part={cell[5]}"
        )
    for quotient in sorted(by_quotient):
        high_beta = [cell for cell in by_quotient[quotient] if cell[2] > 4.0]
        if not high_beta:
            continue
        worst = max(high_beta)
        print(
            f"high_beta_quotient={quotient} count={len(high_beta)} "
            f"worst_ratio={worst[0]:.12f} K_eff_r3={worst[0] ** (1/3):.12f} "
            f"p={worst[1]} odd_part={worst[5]}"
        )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
