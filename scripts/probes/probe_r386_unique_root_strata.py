#!/usr/bin/env python3
"""R386: weighted primitive-generator incidence census for depth three.

For every ordered pair of distinct characteristic-zero shadow keys, aggregate the pair weight by
its difference vector z.  For a chosen prime and order-n root g, count the odd exponents a for which
z(g^a)=0.  These are exactly the primitive generators when n is a power of two.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import math

from probe_r305_complete_census import build_n3


def order_n_element(p, n):
    """Find an element of exact 2-power order n in the prime field."""
    for x in range(2, p):
        if pow(x, n, p) == 1 and pow(x, n // 2, p) != 1:
            return x
    raise ValueError(f"no element of order {n} modulo {p}")


def evaluate(row, powers, p):
    return sum(int(row[j]) * powers[j] for j in row.nonzero()[0]) % p


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--top", type=int, default=20)
    args = ap.parse_args()

    n, p = args.n, args.p
    assert n > 1 and n & (n - 1) == 0, "n must be a power of two"
    assert (p - 1) % n == 0
    keys, cnts = build_n3(n)
    g = order_n_element(p, n)
    half = n // 2

    generators = []
    for a in range(1, n, 2):
        powers = [1]
        ga = pow(g, a, p)
        for _ in range(1, half):
            powers.append(powers[-1] * ga % p)
        generators.append((a, powers))

    # Aggregate weights by exact integer difference.  Canonicalize z up to sign, since ordered
    # pairs contribute both z and -z with equal root sets and total weight.
    mass = defaultdict(int)
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            z = tuple(int(x) for x in (keys[i] - keys[j]))
            first = next((x for x in z if x), 0)
            if first < 0:
                z = tuple(-x for x in z)
            mass[z] += 2 * int(cnts[i]) * int(cnts[j])

    rows = []
    by_z = Counter()
    by_mass = Counter()
    support_mass = Counter()
    height_mass = Counter()
    for z, w in mass.items():
        roots = []
        for a, powers in generators:
            value = sum(c * powers[j] for j, c in enumerate(z) if c) % p
            if value == 0:
                roots.append(a)
        Z = len(roots)
        if not Z:
            continue
        supp = sum(c != 0 for c in z)
        height = max(abs(c) for c in z)
        by_z[Z] += 1
        by_mass[Z] += w
        if Z == 1:
            support_mass[supp] += w
            height_mass[height] += w
        rows.append((w, Z, supp, height, roots, z))

    rows.sort(reverse=True)
    total = sum(by_mass.values())
    all_mass = sum(mass.values())
    unique = by_mass[1]
    multi = sum(w * Z for w, Z, *_ in rows if Z >= 2)
    offdiag = sum(w * Z * (Z - 1) for w, Z, *_ in rows)
    print(f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} g={g}")
    print(f"keys={len(keys)} relations={len(mass)} vanishing={len(rows)}")
    print(f"relation counts by Z: {dict(sorted(by_z.items()))}")
    print(f"relation mass by Z: {dict(sorted(by_mass.items()))}")
    print(f"unique_mass={unique} vanishing_mass={total} fraction={unique/total if total else 0:.6f}")
    centered = p * unique - len(generators) * all_mass
    print(
        f"all_relation_mass={all_mass} baseline={len(generators) * all_mass} "
        f"q_unique={p * unique} centered={centered} "
        f"density_ratio={p * unique / (len(generators) * all_mass) if all_mass else 0:.6f}"
    )
    print(f"multi_first_moment={multi} offdiag={offdiag} ratio={multi/offdiag if offdiag else 0:.6f}")
    print(f"Z=1 mass by support: {dict(sorted(support_mass.items()))}")
    print(f"Z=1 mass by height: {dict(sorted(height_mass.items()))}")
    print("top vanishing relations:")
    for w, Z, supp, height, roots, z in rows[: args.top]:
        sparse = {j: c for j, c in enumerate(z) if c}
        print(f"  mass={w:>10} Z={Z} supp={supp} height={height} roots={roots} z={sparse}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
