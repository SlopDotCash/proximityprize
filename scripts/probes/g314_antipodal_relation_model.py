#!/usr/bin/env python3
"""G314 exact antipodal-pair model for the G313 all-rank dot table.

G313 found that at the certified Proth prime p=111*2^128+1 and toy order n=16,
the coefficient-1 weighted kernel has zero adjacent-rank alignment at every
rank, while coefficient 2 has positive alignment at every rank.

This probe explains that finite table by an exact antipodal-pair model. Write
the 16th roots as eight pairs {e_j, -e_j}. For each ordered kernel pair (y,z)
and each antipodal root pair, the model keeps only selections of A and B that
balance the signed coordinate in

    coefficient*y - z - sum(A) + sum(B) = 0.

The resulting pure combinatorial counts exactly match the large-field dot table
for coefficients 1 and 2 at every rank r=1..15. The same model does not match
the small p=113,n=16 G297 cell, recording that the small signs include extra
finite-field coincidences not present in this certified scale audit.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
from tempfile import gettempdir


N = 16
SMALL_P = 113
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1
COEFFICIENTS = (1, 2)


EXPECTED_MODEL_DOTS = {
    1: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    2: [
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
    ],
}

EXPECTED_SMALL = {
    5: {
        1: (-2_977_296, 17_983_728),
        2: (1_727_120, 18_025_360),
    },
    6: {
        1: (152_176, 79_245_680),
        2: (-77_440, 79_243_648),
    },
}


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
    assert_antipodal(out, p)
    return out


def assert_antipodal(group: list[int], p: int) -> None:
    half = len(group) // 2
    for i in range(half):
        assert (group[i] + group[i + half]) % p == 0


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


def field_alignments(
    group: list[int],
    p: int,
    max_r: int,
    coefficients: tuple[int, ...],
) -> dict[int, list[tuple[int, int]]]:
    dp = subset_hist_sparse(group, p, max_r)
    kernels = {coefficient: kernel_sparse(group, p, coefficient) for coefficient in coefficients}
    return {
        coefficient: [
            sparse_alignment_from_dp(dp, kernels[coefficient], p, len(group), r)
            for r in range(1, max_r + 1)
        ]
        for coefficient in coefficients
    }


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


def signed_coordinate(index: int, pair: int, n: int) -> int:
    half = n // 2
    if index == pair:
        return 1
    if index == pair + half:
        return -1
    return 0


def local_balanced_choices(n: int, pair: int, y: int, z: int, coefficient: int) -> list[tuple[int, int]]:
    base = coefficient * signed_coordinate(y, pair, n) - signed_coordinate(z, pair, n)
    out: list[tuple[int, int]] = []
    for a_mask in range(4):
        for b_mask in range(4):
            delta = base
            a_count = 0
            b_count = 0
            if a_mask & 1:
                delta -= 1
                a_count += 1
            if a_mask & 2:
                delta += 1
                a_count += 1
            if b_mask & 1:
                delta += 1
                b_count += 1
            if b_mask & 2:
                delta -= 1
                b_count += 1
            if delta == 0:
                out.append((a_count, b_count))
    return out


def antipodal_model_dot(n: int, r: int, coefficient: int) -> int:
    half = n // 2
    total = 0
    for y in range(n):
        for z in range(n):
            dp: dict[tuple[int, int], int] = {(0, 0): 1}
            for pair in range(half):
                choices = local_balanced_choices(n, pair, y, z, coefficient)
                next_dp: defaultdict[tuple[int, int], int] = defaultdict(int)
                for (a_rank, b_rank), value in dp.items():
                    for a_count, b_count in choices:
                        aa = a_rank + a_count
                        bb = b_rank + b_count
                        if aa <= r and bb <= r - 1:
                            next_dp[(aa, bb)] += value
                dp = dict(next_dp)
            total += dp.get((r, r - 1), 0)
    return total


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_model_table(handle) -> dict[int, list[int]]:
    model = {
        coefficient: [
            antipodal_model_dot(N, r, coefficient)
            for r in range(1, N)
        ]
        for coefficient in COEFFICIENTS
    }
    assert model == EXPECTED_MODEL_DOTS
    emit(handle, "antipodal-pair model dot table")
    for coefficient in COEFFICIENTS:
        emit(handle, f"coefficient={coefficient}: {model[coefficient]}")
    return model


def verify_large_field_equals_model(handle, model: dict[int, list[int]]) -> None:
    p = certify_proth_prime()
    assert p > N * (1 << 128)
    group = subgroup_proth(N)
    rows = field_alignments(group, p, N - 1, COEFFICIENTS)
    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    for coefficient in COEFFICIENTS:
        dots = [dot for _, dot in rows[coefficient]]
        assert dots == model[coefficient]
        emit(handle, f"large field coefficient={coefficient} dots match model: {dots}")

    for r in range(1, N):
        a1, dot1 = rows[1][r - 1]
        a2, dot2 = rows[2][r - 1]
        assert dot1 == 0
        assert dot2 == EXPECTED_MODEL_DOTS[2][r - 1]
        assert a1 < 0 < a2

    for r in (5, 6):
        for coefficient in COEFFICIENTS:
            direct = direct_pair_alignment(group, p, r, coefficient)
            assert direct == rows[coefficient][r - 1]
            emit(
                handle,
                f"direct field cross-check r={r} coefficient={coefficient} "
                f"A={direct[0]:+d} dot={direct[1]}",
            )


def verify_small_field_extra_relations(handle, model: dict[int, list[int]]) -> None:
    group = subgroup_small(SMALL_P, N)
    rows = field_alignments(group, SMALL_P, 6, COEFFICIENTS)
    emit(handle, "small p=113,n=16 field dots exceed/alter the antipodal model")
    for r in (5, 6):
        for coefficient in COEFFICIENTS:
            a_value, field_dot = rows[coefficient][r - 1]
            model_dot = model[coefficient][r - 1]
            assert (a_value, field_dot) == EXPECTED_SMALL[r][coefficient]
            assert field_dot != model_dot
            emit(
                handle,
                f"small r={r} coefficient={coefficient} "
                f"A={a_value:+d} field_dot={field_dot} model_dot={model_dot} "
                f"extra={field_dot - model_dot:+d}",
            )


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g314_antipodal_relation_model.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G314 antipodal relation model")
        model = verify_model_table(handle)
        verify_large_field_equals_model(handle, model)
        verify_small_field_extra_relations(handle, model)
        emit(
            handle,
            "PASS: the certified large-field n=16 all-rank dot table is exactly "
            "the antipodal-pair relation model; the small p=113 cell has extra "
            "finite-field relations.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
