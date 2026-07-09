#!/usr/bin/env python3
"""#466 R59: larger-n stress test for normalized moment-ratio monotonicity.

R58 found that the Wick-normalized nonzero spectral ratios R_r(μ_n) are
nonincreasing through r=10 for n<=32.  This probe pushes the same hypothesis
to n=64 using one representative per μ_n-coset, since |η_b| is coset-constant.
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
    raise RuntimeError("no primitive root")


def subgroup(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    vals = []
    x = 1
    for _ in range(n):
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


def ratios_from_cosets(p: int, n: int, mags2: list[float], max_r: int) -> list[float]:
    # Each coset value has multiplicity n among b != 0.
    sigma2 = n * sum(mags2) / (p - 1)
    out = []
    for r in range(1, max_r + 1):
        sr = n * sum(m**r for m in mags2)
        out.append(sr / ((p - 1) * dfact(2 * r - 1) * sigma2**r))
    return out


def main() -> None:
    for n, max_r in [(64, 24), (128, 16)]:
        p = first_prime_congruent_one(n, n**4)
        if p > 300_000_000:
            print(f"n={n} p={p} skipped: too large for this exact Python probe")
            continue
        H = subgroup(p, n)
        mags = coset_mags2(p, H)
        rs = ratios_from_cosets(p, n, mags, max_r)
        failures = [(i + 1, rs[i], rs[i + 1]) for i in range(len(rs) - 1) if rs[i + 1] > rs[i] + 1e-9]
        print(f"n={n} p={p} cosets={len(mags)} max_r={max_r} monotone={not failures}")
        print("  head " + " ".join(f"R{r+1}={rs[r]:.6f}" for r in range(min(10, max_r))))
        print("  tail " + " ".join(f"R{max_r-4+i}={rs[max_r-5+i]:.6g}" for i in range(5)))
        if failures:
            print("  failures " + "; ".join(f"R{r}={a:.6g} < R{r+1}={b:.6g}" for r, a, b in failures[:5]))


if __name__ == "__main__":
    main()
