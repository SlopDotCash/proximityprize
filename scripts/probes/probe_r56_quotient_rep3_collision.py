#!/usr/bin/env python3
"""Exact quotient-rep3 probe for #466 R55/R56.

Hypothesis under test:
  Since rep3_G(c) is constant on multiplicative cosets of G, perhaps the
  quotient values obey a stronger low-collision law than the ambient
  Gauss-period/moment wall.  If true, it would be a new route to the
  depth-3 flatness bound.  If false, the quotient lens is only a
  normalization of the same pair-collision object.

The probe computes, for small dyadic n and Burgess-shape primes p ~ n^4:
  * exact rep3(c) for G = μ_n in F_p
  * constancy on G-cosets (sanity check)
  * collision surplus sum_c binom(rep3(c), 2)
  * R3 = S_3 / ((p-1) * 15 * sigma^6) from the period side

No external dependencies.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb, isqrt, log


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def first_prime_congruent_one(n: int, start: int) -> int:
    p = start + ((1 - start) % n)
    while not is_prime(p):
        p += n
    return p


def factor(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError(f"no primitive root for {p}")


def subgroup_mu_n(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    vals = []
    x = 1
    for _ in range(n):
        vals.append(x)
        x = (x * step) % p
    return vals


def periods(p: int, G: list[int]) -> list[complex]:
    # Direct complex periods are enough for small sanity ratios.
    import cmath

    zeta = cmath.exp(2j * cmath.pi / p)
    return [sum(zeta ** ((b * x) % p) for x in G) for b in range(1, p)]


def analyze(n: int) -> dict[str, float | int | bool]:
    p = first_prime_congruent_one(n, n**4)
    G = subgroup_mu_n(p, n)
    Gset = set(G)

    rep = Counter()
    for x in G:
        for y in G:
            xy = (x + y) % p
            for z in G:
                rep[(xy + z) % p] += 1

    # R56 sanity: rep is constant on nonzero multiplicative cosets of G.
    coset_bad = False
    seen = set()
    coset_values: list[int] = []
    for c in range(1, p):
        if c in seen:
            continue
        orbit = {(c * a) % p for a in Gset}
        seen |= orbit
        vals = {rep[o] for o in orbit}
        if len(vals) != 1:
            coset_bad = True
        coset_values.append(next(iter(vals)))

    total = sum(rep.values())
    collision_surplus = sum(comb(v, 2) for v in rep.values())
    max_rep = max(rep.values()) if rep else 0
    support = sum(1 for v in rep.values() if v)
    zero_value = rep[0]
    quotient_nonzero = sum(1 for v in coset_values if v)
    quotient_max = max(coset_values) if coset_values else 0

    etas = periods(p, G)
    s2 = sum(abs(e) ** 2 for e in etas)
    s6 = sum(abs(e) ** 6 for e in etas)
    sigma2 = s2 / (p - 1)
    r3 = s6 / ((p - 1) * 15 * sigma2**3)

    return {
        "n": n,
        "p": p,
        "beta": log(p) / log(n),
        "total_triples": total,
        "support": support,
        "max_rep3": max_rep,
        "zero_rep3": zero_value,
        "collision_surplus": collision_surplus,
        "collision_surplus_over_n2": collision_surplus / (n * n),
        "coset_constancy_ok": not coset_bad,
        "quotient_nonzero_cosets": quotient_nonzero,
        "quotient_max_rep3": quotient_max,
        "r3_subwick_ratio": r3,
        "n_times_deficit": n * (1 - r3),
    }


def main() -> None:
    for n in [8, 16, 32]:
        row = analyze(n)
        print(
            "n={n} p={p} beta={beta:.3f} "
            "support={support}/{p} max_rep3={max_rep3} zero_rep3={zero_rep3} "
            "coll/n^2={collision_surplus_over_n2:.3f} "
            "coset_ok={coset_constancy_ok} qnz={quotient_nonzero_cosets} qmax={quotient_max_rep3} "
            "R3={r3_subwick_ratio:.6f} n(1-R3)={n_times_deficit:.3f}".format(**row)
        )


if __name__ == "__main__":
    main()
