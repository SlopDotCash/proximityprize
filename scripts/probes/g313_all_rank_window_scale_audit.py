#!/usr/bin/env python3
"""G313 exact all-rank scale audit for the coefficient-2 CORE window.

This probe ties together the G300 window-sign oscillation and the G297
coefficient-anchor warning, then checks the same adjacent-rank CORE object at
the certified Proth prime

    p = 111*2^128 + 1.

For toy order n=16 at that field scale, coefficient 1 has zero exact alignment
at every rank r=1..15, while coefficient 2 is positive at every rank. This is
only a finite scale audit: it is not a production n=2^30 theorem and not a
prize closure.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
from tempfile import gettempdir


SMALL_G300_P = 113
SMALL_G300_N = 8
SMALL_G297_P = 113
N = 16
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1


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


def sparse_alignment_from_dp(
    dp: list[dict[int, int]],
    kernel: dict[int, int],
    p: int,
    n: int,
    r: int,
) -> tuple[int, int]:
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


def alignments(group: list[int], p: int, max_r: int, coefficients: tuple[int, ...]) -> dict[int, list[tuple[int, int]]]:
    dp = subset_hist_sparse(group, p, max_r)
    kernels = {coefficient: kernel_sparse(group, p, coefficient) for coefficient in coefficients}
    return {
        coefficient: [
            sparse_alignment_from_dp(dp, kernels[coefficient], p, len(group), r)
            for r in range(1, max_r + 1)
        ]
        for coefficient in coefficients
    }


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def sign(x: int) -> int:
    return 1 if x > 0 else -1 if x < 0 else 0


def verify_g300_small(handle) -> None:
    group = subgroup_small(SMALL_G300_P, SMALL_G300_N)
    rows = alignments(group, SMALL_G300_P, SMALL_G300_N - 1, (2,))[2]
    sequence = [a for a, _ in rows]
    expected = [392, 128, -7240, -13128, -13128, -7240, 128]
    assert sequence == expected
    assert sign(sequence[1]) > 0 and sign(sequence[3]) < 0 and sign(sequence[6]) > 0
    emit(
        handle,
        "G300 check p=113 n=8 coefficient=2 A_r="
        f"{sequence} (small window oscillates)",
    )


def verify_g297_small(handle) -> None:
    group = subgroup_small(SMALL_G297_P, N)
    rows = alignments(group, SMALL_G297_P, 6, (1, 2))
    expected = {
        5: (-2_977_296, 1_727_120),
        6: (152_176, -77_440),
    }
    emit(handle, "G297 check p=113 n=16 coefficients 1 and 2")
    for r in (5, 6):
        a1, dot1 = rows[1][r - 1]
        a2, dot2 = rows[2][r - 1]
        assert (a1, a2) == expected[r]
        emit(handle, f"small r={r} A1={a1:+d} A2={a2:+d} dots=({dot1},{dot2})")


def verify_large_all_ranks(handle) -> None:
    p = certify_proth_prime()
    assert p > N * (1 << 128)
    group = subgroup_proth(N)
    rows = alignments(group, p, N - 1, (1, 2))
    expected_a2_dots = [
        16,
        576,
        8064,
        64064,
        321216,
        1064448,
        2369472,
        3544608,
        3544608,
        2369472,
        1064448,
        321216,
        64064,
        8064,
        576,
    ]

    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    emit(handle, "rank table: r A1 dot1 A2 dot2")
    for r in range(1, N):
        a1, dot1 = rows[1][r - 1]
        a2, dot2 = rows[2][r - 1]
        total = comb(N, r) * comb(N, r - 1)
        assert dot1 == 0
        assert a1 == -(N * N * total)
        assert dot2 == expected_a2_dots[r - 1]
        assert a1 < 0 < a2
        emit(handle, f"{r:2d} {a1:+d} {dot1} {a2:+d} {dot2}")

    for coefficient in (1, 2):
        seq = [a for a, _ in rows[coefficient]]
        for r in range(2, N):
            assert seq[r - 1] == seq[(N + 1 - r) - 1]

    for r in (5, 6):
        for coefficient in (1, 2):
            sparse = rows[coefficient][r - 1]
            direct = direct_pair_alignment(group, p, r, coefficient)
            assert direct == sparse
            emit(
                handle,
                f"direct cross-check r={r} coefficient={coefficient} "
                f"A={direct[0]:+d} dot={direct[1]}",
            )


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g313_all_rank_window_scale_audit.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G313 all-rank window scale audit")
        verify_g300_small(handle)
        verify_g297_small(handle)
        verify_large_all_ranks(handle)
        emit(
            handle,
            "PASS: at certified Proth-prime scale for n=16, coefficient 1 is "
            "negative and coefficient 2 is positive for every adjacent rank r=1..15.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
