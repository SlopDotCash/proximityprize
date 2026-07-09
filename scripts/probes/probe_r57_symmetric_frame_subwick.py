#!/usr/bin/env python3
"""#466 R57: test a possible sub-Wick bypass.

Candidate theorem under attack:
  For any symmetric subset S = -S of F_p^* with |S|=n, the nonzero Fourier
  spectrum eta_b = sum_{x in S} e_p(bx) is sub-Wick:

      R_r(S) := sum_{b!=0} |eta_b|^(2r)
                / ((p-1) (2r-1)!! sigma^(2r)) <= 1.

If true, this would be a big bypass: the prize's moment route would follow
from a general bounded-cosine/negative-dependence frame theorem, not from the
special BGK/Paley structure of multiplicative subgroups.

This probe tries to refute that theorem by sampling random symmetric sets and
hill-climbing for super-Wick examples.  It also prints the dyadic subgroup
baseline in the same field.
"""

from __future__ import annotations

import cmath
import math
import random
from dataclasses import dataclass


random.seed(46657)


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


def dyadic_subgroup(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = (x * step) % p
    return out


def dfact(m: int) -> float:
    out = 1.0
    while m > 0:
        out *= m
        m -= 2
    return out


@dataclass
class Spectrum:
    max_abs: float
    ratios: dict[int, float]


def spectrum(p: int, S: list[int], rs: tuple[int, ...]) -> Spectrum:
    zeta = cmath.exp(2j * math.pi / p)
    mags2 = []
    for b in range(1, p):
        z = sum(zeta ** ((b * x) % p) for x in S)
        mags2.append((z.real * z.real) + (z.imag * z.imag))
    sigma2 = sum(mags2) / len(mags2)
    ratios = {}
    for r in rs:
        sr = sum(m**r for m in mags2)
        ratios[r] = sr / ((p - 1) * dfact(2 * r - 1) * sigma2**r)
    return Spectrum(math.sqrt(max(mags2)), ratios)


def symmetric_set_from_pairs(p: int, reps: set[int]) -> list[int]:
    out = []
    for x in reps:
        out.append(x)
        out.append((-x) % p)
    return out


def random_symmetric_reps(p: int, m: int) -> set[int]:
    reps: set[int] = set()
    banned = {0}
    while len(reps) < m:
        x = random.randrange(1, p)
        y = (-x) % p
        if x in banned or y in banned:
            continue
        reps.add(min(x, y))
        banned.add(x)
        banned.add(y)
    return reps


def mutate_reps(p: int, reps: set[int]) -> set[int]:
    out = set(reps)
    victim = random.choice(tuple(out))
    out.remove(victim)
    banned = {0}
    for x in out:
        banned.add(x)
        banned.add((-x) % p)
    while True:
        x = random.randrange(1, p)
        y = (-x) % p
        rep = min(x, y)
        if x not in banned and y not in banned:
            out.add(rep)
            return out


def search(p: int, n: int, samples: int = 120, steps: int = 120) -> None:
    rs = (2, 3, 4)
    m = n // 2
    subgroup = dyadic_subgroup(p, n)
    base = spectrum(p, subgroup, rs)
    print(f"n={n} p={p} dyadic max={base.max_abs:.3f} " +
          " ".join(f"R{r}={base.ratios[r]:.4f}" for r in rs))

    best_reps = random_symmetric_reps(p, m)
    best = spectrum(p, symmetric_set_from_pairs(p, best_reps), rs)
    random_super = 0
    for _ in range(samples):
        reps = random_symmetric_reps(p, m)
        sp = spectrum(p, symmetric_set_from_pairs(p, reps), rs)
        if max(sp.ratios.values()) > 1:
            random_super += 1
        if sp.ratios[4] > best.ratios[4]:
            best_reps, best = reps, sp

    cur_reps, cur = set(best_reps), best
    temp = 0.002
    for _ in range(steps):
        cand_reps = mutate_reps(p, cur_reps)
        cand = spectrum(p, symmetric_set_from_pairs(p, cand_reps), rs)
        delta = cand.ratios[4] - cur.ratios[4]
        if delta > 0 or random.random() < math.exp(delta / temp):
            cur_reps, cur = cand_reps, cand
        if cur.ratios[4] > best.ratios[4]:
            best_reps, best = set(cur_reps), cur

    print(f"  random symmetric super-Wick samples: {random_super}/{samples}")
    print(f"  best symmetric max={best.max_abs:.3f} " +
          " ".join(f"R{r}={best.ratios[r]:.4f}" for r in rs))
    print(f"  best reps={sorted(best_reps)[:12]}{'...' if len(best_reps) > 12 else ''}")


def main() -> None:
    # Keep p modest enough for exact full spectra and enough room for random symmetric sets.
    for n in (8, 12, 16):
        p = first_prime_congruent_one(n, max(2000, n**3))
        search(p, n)


if __name__ == "__main__":
    main()
