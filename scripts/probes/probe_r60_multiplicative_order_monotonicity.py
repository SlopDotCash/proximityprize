#!/usr/bin/env python3
"""#466 R60: is normalized moment-ratio monotonicity dyadic-specific?

R58/R59 found R_{r+1}(μ_n) <= R_r(μ_n) for 2-power subgroups.
This probe tests multiplicative subgroups of non-dyadic orders.  If monotonicity
fails there, the surviving theorem must use 2-power/cyclotomic structure rather
than only "multiplicative subgroup".
"""

from __future__ import annotations

import math


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def first_prime_congruent_one(order: int, start: int) -> int:
    p = start + ((1 - start) % order)
    while not is_prime(p):
        p += order
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
    raise RuntimeError("no primitive root")


def subgroup(p: int, order: int) -> list[int]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // order, p)
    vals = []
    x = 1
    for _ in range(order):
        vals.append(x)
        x = (x * step) % p
    return vals


def dfact(m: int) -> float:
    out = 1.0
    while m > 0:
        out *= m
        m -= 2
    return out


def coset_mags2(p: int, H: list[int]) -> list[float]:
    seen = bytearray(p)
    w = 2.0 * math.pi / p
    mags = []
    for b in range(1, p):
        if seen[b]:
            continue
        sr = 0.0
        si = 0.0
        for h in H:
            y = (b * h) % p
            seen[y] = 1
            ang = w * y
            sr += math.cos(ang)
            si += math.sin(ang)
        mags.append(sr * sr + si * si)
    return mags


def ratios_from_cosets(p: int, order: int, mags2: list[float], max_r: int) -> list[float]:
    sigma2 = order * sum(mags2) / (p - 1)
    return [
        order * sum(m**r for m in mags2) / ((p - 1) * dfact(2 * r - 1) * sigma2**r)
        for r in range(1, max_r + 1)
    ]


def monotone_failures(rs: list[float]) -> list[tuple[int, float, float]]:
    return [(i + 1, rs[i], rs[i + 1]) for i in range(len(rs) - 1) if rs[i + 1] > rs[i] + 1e-9]


def main() -> None:
    max_r = 12
    orders = [9, 12, 15, 18, 20, 24, 27, 30, 32, 36, 40, 48]
    for order in orders:
        p = first_prime_congruent_one(order, order**4)
        if p > 25_000_000:
            print(f"order={order:2d} p={p} skipped")
            continue
        H = subgroup(p, order)
        rs = ratios_from_cosets(p, order, coset_mags2(p, H), max_r)
        fails = monotone_failures(rs)
        parity = "even" if order % 2 == 0 else "odd"
        dyadic = order & (order - 1) == 0
        tag = "2pow" if dyadic else parity
        print(
            f"order={order:2d} tag={tag:4s} p={p:9d} mono={not fails} "
            + " ".join(f"R{r+1}={rs[r]:.4f}" for r in range(6))
        )
        if fails:
            print("  first failures " + "; ".join(
                f"R{r}={a:.5f} < R{r+1}={b:.5f}" for r, a, b in fails[:4]
            ))


if __name__ == "__main__":
    main()
