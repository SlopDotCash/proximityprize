#!/usr/bin/env python3
"""#466 R62: high-order stress test for the six-resonance boundary.

R61 found Wick-normalized moment monotonicity failures exactly at the visible
multiples of 6 from 18 upward.  This probe pushes that pattern to larger
orders using primes p = 1 mod order near order^3, which keeps the exact coset
spectrum affordable while testing the structural boundary well past the R61
range.
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
    step = pow(primitive_root(p), (p - 1) // order, p)
    out = []
    x = 1
    for _ in range(order):
        out.append(x)
        x = (x * step) % p
    return out


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


def ratios(p: int, order: int, mags2: list[float], max_r: int) -> list[float]:
    sigma2 = order * sum(mags2) / (p - 1)
    return [
        order * sum(m**r for m in mags2) / ((p - 1) * dfact(2 * r - 1) * sigma2**r)
        for r in range(1, max_r + 1)
    ]


def first_failure(rs: list[float]) -> tuple[int, float, float] | None:
    for i in range(len(rs) - 1):
        if rs[i + 1] > rs[i] + 1e-9:
            return i + 1, rs[i], rs[i + 1]
    return None


def main() -> None:
    orders = [
        62, 64, 68, 70, 72, 74, 76, 78, 80, 82, 84, 88, 90, 92, 96,
        100, 102, 104, 108, 110, 112, 114, 118, 120,
    ]
    max_r = 10
    print("order p        div6 status first-failure       maxR")
    print("-" * 64)
    mismatches = []
    for order in orders:
        p = first_prime_congruent_one(order, order**3)
        rs = ratios(p, order, coset_mags2(p, subgroup(p, order)), max_r)
        fail = first_failure(rs)
        predicted = order % 6 == 0 and order >= 18
        observed = fail is not None
        if predicted != observed:
            mismatches.append(order)
        status = "FAIL" if observed else "OK"
        ff = "-" if fail is None else f"R{fail[0]}={fail[1]:.4f}<R{fail[0]+1}={fail[2]:.4f}"
        print(f"{order:5d} {p:8d} {str(order % 6 == 0):4s} {status:6s} {ff:20s} {max(rs):.4f}")

    print("\nsummary")
    print("mismatches:", " ".join(map(str, mismatches)) if mismatches else "none")


if __name__ == "__main__":
    main()
