#!/usr/bin/env python3
"""Exact G136/G139 normalized accident census at production-like cells.

For H = mu_n(F_p), count triples (a,b,c) in H^3 satisfying

    a + b = c + 1

and exclude the three lawful Mann families from G136:

    (1,b,b), (a,1,a), (a,-a,-1).

The selected cells are the first primes p = 1 mod n at scale
p ~= n^(158/30).  The target scale is found using exact integer nth-root
arithmetic; floating point is used only to print the diagnostic log value.

Honest scope: finite exact-arithmetic evidence only.  This is not a proof at
n = 2^30 and not a prize closure.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from math import log

BETA_NUM = 158
BETA_DEN = 30


@dataclass(frozen=True)
class CensusRow:
    n: int
    p: int
    beta: float
    v2_pm1: int
    total_solutions: int
    lawful_solutions: int
    accidents: int
    four_divides_accidents: bool


def floor_nth_root(a: int, n: int) -> int:
    """Return floor(a^(1/n)) using integer arithmetic."""
    if a < 0 or n <= 0:
        raise ValueError("expected a >= 0 and n > 0")
    if a < 2:
        return a
    lo, hi = 1, 1
    while hi**n <= a:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**n <= a:
            lo = mid
        else:
            hi = mid
    return lo


def rounded_rational_power(n: int, num: int, den: int) -> int:
    """Return round(n^(num/den)) using exact integer comparisons."""
    base = n**num
    root = floor_nth_root(base, den)
    lower_gap = base - root**den
    upper_gap = (root + 1) ** den - base
    if upper_gap < lower_gap:
        return root + 1
    return root


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    # Deterministic for this run: all tested p are below 341,550,071,728,321.
    for a in (2, 3, 5, 7, 11, 13, 17):
        if a >= n:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor_rad(n: int) -> list[int]:
    out: list[int] = []
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


def v2(n: int) -> int:
    out = 0
    while n % 2 == 0:
        out += 1
        n //= 2
    return out


def first_production_like_prime(n: int) -> int:
    target = rounded_rational_power(n, BETA_NUM, BETA_DEN)
    k = max(1, target // n)
    if k % 2 == 0:
        k += 1
    while True:
        p = n * k + 1
        if is_prime(p):
            return p
        k += 2


def primitive_root(p: int) -> int:
    qs = factor_rad(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
    raise RuntimeError(f"no primitive root found for p={p}")


def subgroup_mu_n(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    omega = pow(g, (p - 1) // n, p)
    h: list[int] = []
    x = 1
    for _ in range(n):
        h.append(x)
        x = (x * omega) % p
    assert x == 1
    assert len(set(h)) == n
    assert pow(omega, n, p) == 1
    assert pow(omega, n // 2, p) == p - 1
    return h


def is_lawful(a: int, b: int, c: int, p: int) -> bool:
    return (
        (a == 1 and c == b)
        or (b == 1 and c == a)
        or (c == p - 1 and b == (-a) % p)
    )


def census(h: list[int], p: int) -> tuple[int, list[tuple[int, int, int]]]:
    hs = set(h)
    total = 0
    accidents: list[tuple[int, int, int]] = []
    for a in h:
        for b in h:
            c = (a + b - 1) % p
            if c not in hs:
                continue
            total += 1
            if not is_lawful(a, b, c, p):
                accidents.append((a, b, c))
    return total, accidents


def solution_count_by_sums(h: list[int], p: int) -> int:
    """Independent total-solution count, without Mann-family predicates."""
    sums = Counter((a + b) % p for a in h for b in h)
    hs = set(h)
    return sum(count for s, count in sums.items() if (s - 1) % p in hs)


def census_row(n: int) -> CensusRow:
    p = first_production_like_prime(n)
    h = subgroup_mu_n(p, n)
    total, accidents = census(h, p)
    lawful = 3 * n - 3
    assert total == lawful + len(accidents)
    total_by_sums = solution_count_by_sums(h, p)
    assert total_by_sums == total
    assert total_by_sums - lawful == len(accidents)
    return CensusRow(
        n=n,
        p=p,
        beta=log(p, n),
        v2_pm1=v2(p - 1),
        total_solutions=total,
        lawful_solutions=lawful,
        accidents=len(accidents),
        four_divides_accidents=(len(accidents) % 4 == 0),
    )


def check_g173_witness() -> None:
    p, n, omega = 17318209, 64, 7937154
    h = [pow(omega, i, p) for i in range(n)]
    assert len(set(h)) == n
    assert pow(omega, n, p) == 1
    assert pow(omega, n // 2, p) == p - 1
    total, accidents = census(h, p)
    witness = (pow(omega, 52, p), pow(omega, 57, p), pow(omega, 58, p))
    assert witness == (5663213, 17079628, 5424631)
    assert witness in accidents
    print(
        "G173 cross-check: "
        f"n={n} p={p} total_solutions={total} accidents={len(accidents)} "
        f"witness={witness}"
    )


def main() -> None:
    check_g173_witness()
    print("production-like cells:")
    print("n,p,log_p_base_n,v2(p-1),total,lawful,accidents,4|accidents")
    for n in (16, 32, 64, 128, 256):
        row = census_row(n)
        print(
            f"{row.n},{row.p},{row.beta:.9f},{row.v2_pm1},"
            f"{row.total_solutions},{row.lawful_solutions},"
            f"{row.accidents},{row.four_divides_accidents}"
        )


if __name__ == "__main__":
    main()
