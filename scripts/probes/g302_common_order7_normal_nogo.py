#!/usr/bin/env python3
"""Exact G302 sponsor-common order-seven weighted-kernel no-go.

For sponsor quotient orders m1=2^128+192 and m2=2^129+13, gcd(m1,m2)=7.
Thus the only common nonprincipal fixed character order is seven. For every manageable
dyadic cell with 7 | m=(p-1)/n and 2 outside the subgroup, this probe computes the
canonical primitive-order-seven Ramanujan aggregate

    L7(r) = sum_{j mod m} c7(j) A_{g^j}(R_r),
    c7(j) = 6 if 7|j else -1,

using only exact Python integer arithmetic. It verifies generator independence, all
marginal masses, chance-level sign agreement, and both mismatch polarities.
"""
from __future__ import annotations

from math import comb, gcd


def factors(n: int) -> list[int]:
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


def primitive_root(p: int) -> int:
    fs = factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError(f"no primitive root mod {p}")


def subgroup(p: int, n: int, g: int) -> list[int]:
    h = pow(g, (p - 1) // n, p)
    out: list[int] = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * h % p
    assert x == 1 and len(set(out)) == n
    return out


def subset_hist(group: list[int], p: int, max_r: int) -> list[list[int]]:
    dp = [[0] * p for _ in range(max_r + 1)]
    dp[0][0] = 1
    used = 0
    for x in group:
        used += 1
        for r in range(min(used, max_r), 0, -1):
            prev = dp[r - 1]
            cur = dp[r]
            for s, value in enumerate(prev):
                if value:
                    cur[(s + x) % p] += value
    for r in range(max_r + 1):
        assert sum(dp[r]) == comb(len(group), r)
    return dp


def difference_corr(left: list[int], right: list[int], p: int) -> list[int]:
    out = [0] * p
    for x, vx in enumerate(left):
        if vx:
            for y, vy in enumerate(right):
                if vy:
                    out[(x - y) % p] += vx * vy
    assert sum(out) == sum(left) * sum(right)
    return out


def weighted_kernel(group: list[int], p: int, coefficient: int) -> list[int]:
    out = [0] * p
    for y in group:
        ay = coefficient * y % p
        for z in group:
            out[(ay - z) % p] += 1
    assert sum(out) == len(group) ** 2
    return out


def alignment(kernel: list[int], row: list[int], p: int, n: int) -> int:
    return p * sum(x * y for x, y in zip(kernel, row)) - n * n * sum(row)


def sign(x: int) -> int:
    return (x > 0) - (x < 0)


def weight7(j: int) -> int:
    return 6 if j % 7 == 0 else -1


def run_cell(n: int, p: int) -> list[tuple[int, int, int]]:
    g = primitive_root(p)
    m = (p - 1) // n
    group = subgroup(p, n, g)
    assert m % 7 == 0 and pow(2, n, p) != 1
    hist = subset_hist(group, p, 6)
    reps = [pow(g, j, p) for j in range(m)]
    kernels = [weighted_kernel(group, p, a) for a in reps]
    kernel2 = weighted_kernel(group, p, 2)
    rows: list[tuple[int, int, int]] = []
    for r in (5, 6):
        row = difference_corr(hist[r], hist[r - 1], p)
        values = [alignment(kernel, row, p, n) for kernel in kernels]
        normal = sum(weight7(j) * value for j, value in enumerate(values))
        target = alignment(kernel2, row, p, n)
        # Changing the quotient generator permutes positions by a unit. The
        # primitive-order-seven trace is invariant under every such change.
        for u in range(1, m):
            if gcd(u, m) == 1:
                changed = sum(weight7(j) * values[(u * j) % m] for j in range(m))
                assert changed == normal
        rows.append((r, target, normal))
    return rows


def main() -> None:
    sponsor_m1 = 2**128 + 192
    sponsor_m2 = 2**129 + 13
    assert gcd(sponsor_m1, sponsor_m2) == 7
    print(f"sponsor m1={sponsor_m1} m2={sponsor_m2} gcd=7")

    cells: list[tuple[int, int, int, list[tuple[int, int, int]]]] = []
    for n, limit in ((8, 2200), (16, 3000), (32, 5000)):
        for p in range(7 * n + 1, limit + 1):
            if not is_prime(p) or (p - 1) % n:
                continue
            m = (p - 1) // n
            if m % 7 or pow(2, n, p) == 1:
                continue
            cells.append((n, p, m, run_cell(n, p)))

    assert cells
    agree = 0
    total = 0
    quadrants: set[tuple[int, int]] = set()
    representatives: dict[tuple[int, int], tuple[int, int, int, int, int, int]] = {}
    for n, p, m, rows in cells:
        for r, target, normal in rows:
            assert target and normal
            pair = (sign(target), sign(normal))
            total += 1
            agree += pair[0] == pair[1]
            quadrants.add(pair)
            representatives.setdefault(pair, (n, p, m, r, target, normal))

    print(f"cells={len(cells)} rankcells={total} sign_agree={agree}/{total}")
    for pair in sorted(representatives):
        n, p, m, r, target, normal = representatives[pair]
        print(
            f"quadrant={pair} n={n} p={p} m={m} r={r} "
            f"A2={target:+d} L7={normal:+d}"
        )

    # Same-prime, same-subgroup adjacent-rank mismatch reversal.
    witness = run_cell(16, 113)
    assert witness == [
        (5, 1727120, -20424976),
        (6, -77440, 1048640),
    ]
    assert total == 54 and agree == 27 and len(quadrants) == 4
    print(
        "PASS: the unique common nonprincipal bounded sponsor order is seven; "
        "its canonical generator-independent trace is sign-decoupled in all four quadrants."
    )


if __name__ == "__main__":
    main()
