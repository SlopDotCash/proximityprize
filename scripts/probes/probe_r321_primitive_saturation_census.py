#!/usr/bin/env python3
"""#466 R321: primitive-recurrence saturation across all depth-4 K-bad cells.

For each of the 92 n=32 in-window K-bad primes, find the signed shift-orbit
carrying the most shadow collision mass.  If f is its relation polynomial,
compute |Res(x^16+1,f)| / p.  A power-of-two quotient means the principal
circulant recurrence lattice has only dyadic index inside the full evaluation
kernel lattice.
"""

from __future__ import annotations

import re
from collections import Counter, defaultdict
from pathlib import Path

import sympy as sp

from probe_r307_binomial_norm_depth3 import order_n_element
from probe_r320_collision_orbit_coherence import orbit_key, shadow_histogram


ROW = re.compile(r"^(\d+)\s+\d+\s+[0-9.]+\s+\S+\s+\d+\s+\d+\s+(\d+)\s+")


def main() -> int:
    n, r, m = 32, 4, 16
    hist = shadow_histogram(n, r)
    rows = []
    for line in Path("scripts/probes/_out_466_d4_structure.txt").read_text().splitlines():
        match = ROW.match(line)
        if match:
            rows.append(tuple(map(int, match.groups())))

    x = sp.symbols("x")
    cyclotomic = x**m + 1
    quotient_hist = Counter()
    shares = []
    examples = []
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
        power_two = remainder == 0 and quotient > 0 and quotient & (quotient - 1) == 0
        if not power_two:
            failures.append((p, resultant, quotient, remainder))
        quotient_hist[quotient] += 1
        shares.append(top_mass / total)
        if p in (1065409, 1439393, 4102753):
            examples.append((p, top_mass / total, quotient, key))

    print("# R321 primitive-recurrence dyadic saturation census")
    print(
        f"n={n} r={r} cells={len(rows)} shadow_keys={len(hist)} "
        f"quotient_hist={dict(sorted(quotient_hist.items()))} failures={len(failures)}"
    )
    print(
        f"top_orbit_share min={min(shares):.9f} mean={sum(shares)/len(shares):.9f} "
        f"max={max(shares):.9f}"
    )
    for p, share, quotient, key in examples:
        print(f"example p={p} share={share:.9f} resultant_quotient={quotient} relation={key}")
    for failure in failures:
        print(f"failure={failure}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
