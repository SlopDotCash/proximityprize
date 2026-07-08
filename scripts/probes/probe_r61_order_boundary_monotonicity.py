#!/usr/bin/env python3
"""#466 R61: classify the order boundary for normalized monotonicity.

R60 found failures for several even non-2-power subgroup orders but not all.
This broader sweep tests orders 6..72 and records the first monotonicity
failure of the Wick-normalized ratios R_r.
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


def factor_mult(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def factor(n: int) -> list[int]:
    return list(factor_mult(n).keys())


def primitive_root(p: int) -> int:
    fac = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")


def subgroup(p: int, order: int) -> list[int]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // order, p)
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


def ratios_from_cosets(p: int, order: int, mags2: list[float], max_r: int) -> list[float]:
    sigma2 = order * sum(mags2) / (p - 1)
    return [
        order * sum(m**r for m in mags2) / ((p - 1) * dfact(2 * r - 1) * sigma2**r)
        for r in range(1, max_r + 1)
    ]


def first_failure(rs: list[float]) -> tuple[int, float, float] | None:
    for i in range(len(rs) - 1):
        if rs[i + 1] > rs[i] + 1e-9:
            return (i + 1, rs[i], rs[i + 1])
    return None


def tag(order: int) -> str:
    fac = factor_mult(order)
    odd = order
    while odd % 2 == 0:
        odd //= 2
    if odd == 1:
        return "2pow"
    return f"2^{fac.get(2, 0)}*{odd}"


def main() -> None:
    max_r = 10
    rows = []
    for order in range(6, 73):
        p = first_prime_congruent_one(order, order**4)
        if p > 12_000_000:
            continue
        H = subgroup(p, order)
        rs = ratios_from_cosets(p, order, coset_mags2(p, H), max_r)
        fail = first_failure(rs)
        superwick = max((i + 1, x) for i, x in enumerate(rs) if x == max(rs))[1] > 1 + 1e-9
        rows.append((order, tag(order), p, fail, superwick, rs))

    print("order tag      p        status      first-failure       maxR")
    print("-" * 72)
    for order, tg, p, fail, superwick, rs in rows:
        status = "FAIL" if fail else "OK"
        if superwick:
            status += "+SW"
        ff = "-" if fail is None else f"R{fail[0]}={fail[1]:.4f}<R{fail[0]+1}={fail[2]:.4f}"
        print(f"{order:5d} {tg:7s} {p:8d} {status:10s} {ff:24s} {max(rs):.4f}")

    fails = [r for r in rows if r[3] is not None]
    print("\nsummary")
    print(f"tested={len(rows)} failures={len(fails)}")
    print("failure orders:", " ".join(str(r[0]) for r in fails))


if __name__ == "__main__":
    main()
