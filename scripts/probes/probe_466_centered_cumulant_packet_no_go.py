#!/usr/bin/env python3
"""Exact centered partition-cumulant counterexample for issue #466.

For H = mu_8 in F_41, compute raw ordered zero-sum counts through depth four,
center them by subtracting n^m/p, and apply the ordinary distinguished-block
partition cumulant recurrence.  The fourth connected coefficient is negative,
so the center-first recurrence is not a positive packet census.
"""
from fractions import Fraction
from math import comb


def factor(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError(f"no primitive root found for {p}")


def subgroup(n: int, p: int) -> list[int]:
    z = pow(primitive_root(p), (p - 1) // n, p)
    return [pow(z, j, p) for j in range(n)]


def moments(n: int, p: int, depth: int) -> list[int]:
    H = subgroup(n, p)
    dist = [0] * p
    dist[0] = 1
    out = [1]
    for _ in range(1, depth + 1):
        nxt = [0] * p
        for s, a in enumerate(dist):
            if a:
                for x in H:
                    nxt[(s + x) % p] += a
        dist = nxt
        out.append(dist[0])
    return out


def cumulants(M: list[Fraction]) -> list[Fraction]:
    K = [Fraction(0) for _ in M]
    for m in range(1, len(M)):
        K[m] = M[m] - sum(
            Fraction(comb(m - 1, k - 1)) * K[k] * M[m - k]
            for k in range(1, m)
        )
    return K


def main() -> None:
    n, p, depth = 8, 41, 4
    H = subgroup(n, p)
    raw = moments(n, p, depth)
    centered = [Fraction(1)] + [
        Fraction(raw[m] * p - n ** m, p) for m in range(1, depth + 1)
    ]
    K = cumulants(centered)
    expected_raw = [1, 0, 8, 0, 200]
    expected_centered = [
        Fraction(1),
        Fraction(-8, 41),
        Fraction(264, 41),
        Fraction(-512, 41),
        Fraction(4104, 41),
    ]
    expected_k4 = Fraction(-87878392, 2825761)
    assert raw == expected_raw, raw
    assert centered == expected_centered, centered
    assert K[4] == expected_k4, K[4]
    assert K[4] < 0
    print("# centered partition-cumulant packet no-go")
    print(f"H=mu_{n} in F_{p}: {H}")
    print(f"raw zero-sum counts M_0..M_4: {raw}")
    print(f"centered moments Mc_1..Mc_4: {centered[1:]}")
    print(f"Kc_4 = {K[4]} < 0")


if __name__ == "__main__":
    main()
