#!/usr/bin/env python3
"""#466 R58: test normalized moment-ratio monotonicity.

Closing-grade hypothesis:
  For G = μ_n in the Burgess/prize regime, the DC-subtracted normalized ratios

      R_r = Σ_{b≠0}|η_b|^(2r) / ((p-1) (2r-1)!! σ^(2r))

  are nonincreasing in r.

If true as a theorem, the low proven rungs would propagate to the deep moment
depth used by the prize.  This probe tests the shape exactly on feasible
dyadic subgroups and compares against random symmetric sets.
"""

from __future__ import annotations

import cmath
import math
import random

random.seed(46658)


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


def first_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


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


def random_symmetric(p: int, n: int) -> list[int]:
    reps = set()
    banned = {0}
    while len(reps) < n // 2:
        x = random.randrange(1, p)
        y = (-x) % p
        rep = min(x, y)
        if x in banned or y in banned:
            continue
        reps.add(rep)
        banned.add(x)
        banned.add(y)
    return [x for r in reps for x in (r, (-r) % p)]


def dfact(m: int) -> float:
    out = 1.0
    while m > 0:
        out *= m
        m -= 2
    return out


def ratios(p: int, S: list[int], max_r: int) -> list[float]:
    zeta = cmath.exp(2j * math.pi / p)
    mags2 = []
    for b in range(1, p):
        z = sum(zeta ** ((b * x) % p) for x in S)
        mags2.append(z.real * z.real + z.imag * z.imag)
    sigma2 = sum(mags2) / (p - 1)
    out = []
    for r in range(1, max_r + 1):
        sr = sum(m**r for m in mags2)
        out.append(sr / ((p - 1) * dfact(2 * r - 1) * sigma2**r))
    return out


def monotone_nonincreasing(xs: list[float], eps: float = 1e-10) -> bool:
    return all(xs[i + 1] <= xs[i] + eps for i in range(len(xs) - 1))


def main() -> None:
    max_r = 10
    print("dyadic subgroup moment-ratio monotonicity")
    for n in (8, 16, 32):
        count = 6 if n < 32 else 3
        ps = first_primes_congruent_one(n, n**4, count)
        failures = []
        for p in ps:
            rs = ratios(p, subgroup(p, n), max_r)
            if not monotone_nonincreasing(rs):
                failures.append((p, rs))
            print(
                f"n={n:2d} p={p:8d} mono={monotone_nonincreasing(rs)} "
                + " ".join(f"R{r+1}={rs[r]:.4f}" for r in range(min(6, max_r)))
            )
        print(f"  failures: {len(failures)}/{len(ps)}")

    print("\nrandom symmetric controls")
    for n in (8, 12, 16):
        p = first_primes_congruent_one(n, max(2000, n**3), 1)[0]
        bad = 0
        worst_jump = 0.0
        worst = None
        for _ in range(40):
            rs = ratios(p, random_symmetric(p, n), max_r)
            jumps = [rs[i + 1] - rs[i] for i in range(len(rs) - 1)]
            jump = max(jumps)
            if jump > 1e-10:
                bad += 1
            if jump > worst_jump:
                worst_jump = jump
                worst = rs
        print(
            f"n={n:2d} p={p:5d} random monotonicity failures={bad}/40 "
            f"worst_jump={worst_jump:.4f}"
        )
        if worst is not None:
            print("  worst " + " ".join(f"R{r+1}={worst[r]:.3f}" for r in range(6)))


if __name__ == "__main__":
    main()
