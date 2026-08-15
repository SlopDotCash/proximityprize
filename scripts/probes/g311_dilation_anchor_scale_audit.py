#!/usr/bin/env python3
"""G311 exact scale audit for G297's dilation-anchor sign-transport no-go.

G297 shows that the coefficient-1 anchor A_1(R) does not transport its sign to
the coefficient-2 target A_2(R) on the small cell mu_16 <= F_113^*. This probe
reproduces that cell and then checks the same finite question at the certified
Proth prime

    p = 111*2^128 + 1.

For n=16 and r in {5,6}, both independent implementations find A_1 < 0 < A_2.
This is a finite toy-order scale audit only; it is not a production n=2^30
statement and not a prize closure.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
from tempfile import gettempdir


SMALL_P = 113
N = 16
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1
RANKS = (5, 6)


def factor(x: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out


def primitive_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise AssertionError("no primitive root")


def subgroup_from_root(p: int, n: int, root: int) -> list[int]:
    h = pow(root, (p - 1) // n, p)
    out: list[int] = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * h % p
    assert x == 1 and len(set(out)) == n
    return out


def subgroup_small(p: int, n: int) -> list[int]:
    return subgroup_from_root(p, n, primitive_root(p))


def certify_proth_prime() -> int:
    assert PROTH_K % 2 == 1
    assert PROTH_K < (1 << PROTH_M)
    # Proth theorem: this congruence proves PROTH_P is prime.
    assert pow(PROTH_WITNESS, (PROTH_P - 1) // 2, PROTH_P) == PROTH_P - 1
    return PROTH_P


def subgroup_proth(n: int) -> list[int]:
    p = certify_proth_prime()
    assert n & (n - 1) == 0
    assert n <= (1 << PROTH_M)
    return subgroup_from_root(p, n, PROTH_WITNESS)


def subset_hist_sparse(group: list[int], p: int, max_r: int) -> list[dict[int, int]]:
    dp: list[defaultdict[int, int]] = [defaultdict(int) for _ in range(max_r + 1)]
    dp[0][0] = 1
    used = 0
    for x in group:
        used += 1
        for r in range(min(used, max_r), 0, -1):
            for s, value in list(dp[r - 1].items()):
                dp[r][(s + x) % p] += value
    for r in range(max_r + 1):
        assert sum(dp[r].values()) == comb(len(group), r)
    return [dict(row) for row in dp]


def subset_sums_direct(group: list[int], p: int, r: int) -> list[int]:
    out: list[int] = []
    for indices in combinations(range(len(group)), r):
        total = 0
        for i in indices:
            total = (total + group[i]) % p
        out.append(total)
    assert len(out) == comb(len(group), r)
    return out


def kernel_sparse(group: list[int], p: int, coefficient: int) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for y in group:
        ay = coefficient * y % p
        for z in group:
            out[(ay - z) % p] += 1
    assert sum(out.values()) == len(group) ** 2
    return dict(out)


def row_value(left: dict[int, int], right: dict[int, int], p: int, t: int) -> int:
    # R(t) = sum_x left[x] * right[x - t].
    if len(left) <= len(right):
        return sum(value * right.get((x - t) % p, 0) for x, value in left.items())
    return sum(value * left.get((y + t) % p, 0) for y, value in right.items())


def sparse_alignment(group: list[int], p: int, r: int, coefficient: int) -> tuple[int, int]:
    n = len(group)
    dp = subset_hist_sparse(group, p, r)
    kernel = kernel_sparse(group, p, coefficient)
    dot = sum(weight * row_value(dp[r], dp[r - 1], p, t) for t, weight in kernel.items())
    total = comb(n, r) * comb(n, r - 1)
    return p * dot - n * n * total, dot


def direct_pair_alignment(group: list[int], p: int, r: int, coefficient: int) -> tuple[int, int]:
    n = len(group)
    left = subset_sums_direct(group, p, r)
    right = subset_sums_direct(group, p, r - 1)
    kernel = kernel_sparse(group, p, coefficient)
    dot = 0
    for x in left:
        for y in right:
            dot += kernel.get((x - y) % p, 0)
    total = len(left) * len(right)
    assert total == comb(n, r) * comb(n, r - 1)
    return p * dot - n * n * total, dot


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_small(handle) -> None:
    group = subgroup_small(SMALL_P, N)
    expected = {
        5: (-2_977_296, 1_727_120, 4_704_416),
        6: (152_176, -77_440, -229_616),
    }
    emit(handle, "reproducing G297 small cell mu_16 <= F_113^*")
    for r in RANKS:
        a1, dot1 = sparse_alignment(group, SMALL_P, r, 1)
        a2, dot2 = sparse_alignment(group, SMALL_P, r, 2)
        assert (a1, a2, a2 - a1) == expected[r]
        emit(
            handle,
            f"small p={SMALL_P} n={N} r={r} "
            f"A1={a1:+d} A2={a2:+d} delta={a2 - a1:+d} dots=({dot1},{dot2})",
        )


def verify_large(handle) -> None:
    p = certify_proth_prime()
    group = subgroup_proth(N)
    expected = {
        5: (
            -2_035_138_560,
            12_132_759_625_789_254_812_263_498_506_989_117_214_991_787_712,
            0,
            321_216,
        ),
        6: (
            -8_954_609_664,
            40_205_630_224_372_760_716_789_501_328_599_919_806_465_162_752,
            0,
            1_064_448,
        ),
    }
    assert p > N * (1 << 128)
    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    for r in RANKS:
        sparse_a1, sparse_dot1 = sparse_alignment(group, p, r, 1)
        sparse_a2, sparse_dot2 = sparse_alignment(group, p, r, 2)
        direct_a1, direct_dot1 = direct_pair_alignment(group, p, r, 1)
        direct_a2, direct_dot2 = direct_pair_alignment(group, p, r, 2)
        assert (sparse_a1, sparse_a2, sparse_dot1, sparse_dot2) == expected[r]
        assert (direct_a1, direct_a2, direct_dot1, direct_dot2) == expected[r]
        assert sparse_a1 < 0 < sparse_a2
        emit(
            handle,
            f"large p={p} n={N} r={r} "
            f"A1={sparse_a1:+d} A2={sparse_a2:+d} "
            f"delta={sparse_a2 - sparse_a1:+d} dots=({sparse_dot1},{sparse_dot2})",
        )


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g311_dilation_anchor_scale_audit.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G311 dilation-anchor scale audit")
        verify_small(handle)
        verify_large(handle)
        emit(
            handle,
            "PASS: coefficient-1 sign does not transport to coefficient-2 at the "
            "certified Proth-prime scale for n=16, r=5,6.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
