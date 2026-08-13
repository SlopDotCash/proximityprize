#!/usr/bin/env python3
"""G315 exact n=32 live-rank antipodal model check.

G314 explains the certified n=16 all-rank dot table by a pure antipodal-pair
model. G315 stress-tests that mechanism one toy order higher. At the same
certified Proth prime

    p = 111*2^128 + 1,

it checks n=32 at the live ranks r=5 and r=6. The exact finite-field sparse
subset-histogram computation matches the antipodal-pair model: coefficient 1
has zero alignment, while coefficient 2 has positive alignment.

This is still a finite toy-order audit, not a production n=2^30 theorem.
"""
from __future__ import annotations

from collections import defaultdict
from math import comb
from pathlib import Path
from tempfile import gettempdir


N = 32
RANKS = (5, 6)
COEFFICIENTS = (1, 2)
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1


EXPECTED_MODEL_DOTS = {
    1: {5: 0, 6: 0},
    2: {5: 20_115_200, 6: 200_992_512},
}

EXPECTED_A_VALUES = {
    1: {5: -7_415_276_503_040, 6: -186_864_967_876_608},
    2: {
        5: 759_778_113_246_774_813_208_690_492_278_676_928_490_593_775_360,
        6: 7_591_757_056_558_709_115_750_550_940_264_470_531_009_269_655_296,
    },
}

EXPECTED_HIST_SIZES = {
    0: 1,
    1: 32,
    2: 481,
    3: 4512,
    4: 29_601,
    5: 144_288,
    6: 542_113,
}

EXPECTED_KERNEL_SIZES = {
    1: 513,
    2: 1024,
}


def subgroup_from_root(p: int, n: int, root: int) -> list[int]:
    h = pow(root, (p - 1) // n, p)
    out: list[int] = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * h % p
    assert x == 1 and len(set(out)) == n
    half = n // 2
    for i in range(half):
        assert (out[i] + out[i + half]) % p == 0
    return out


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
        assert len(dp[r]) == EXPECTED_HIST_SIZES[r]
    return [dict(row) for row in dp]


def kernel_sparse(group: list[int], p: int, coefficient: int) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for y in group:
        ay = coefficient * y % p
        for z in group:
            out[(ay - z) % p] += 1
    assert sum(out.values()) == len(group) ** 2
    assert len(out) == EXPECTED_KERNEL_SIZES[coefficient]
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


def verify_model(handle) -> None:
    emit(handle, "antipodal-pair model dots for n=32")
    for coefficient in COEFFICIENTS:
        for r in RANKS:
            dot = antipodal_model_dot(N, r, coefficient)
            assert dot == EXPECTED_MODEL_DOTS[coefficient][r]
            emit(handle, f"model coefficient={coefficient} r={r} dot={dot}")


def verify_large_field(handle) -> None:
    p = certify_proth_prime()
    assert p > N * (1 << 128)
    group = subgroup_proth(N)
    dp = subset_hist_sparse(group, p, max(RANKS))
    kernels = {coefficient: kernel_sparse(group, p, coefficient) for coefficient in COEFFICIENTS}

    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    for r in range(max(RANKS) + 1):
        emit(handle, f"hist r={r} support={len(dp[r])} mass={sum(dp[r].values())}")
    for coefficient in COEFFICIENTS:
        emit(handle, f"kernel coefficient={coefficient} support={len(kernels[coefficient])}")
        for r in RANKS:
            a_value, dot = sparse_alignment_from_dp(dp, kernels[coefficient], p, N, r)
            assert dot == EXPECTED_MODEL_DOTS[coefficient][r]
            assert a_value == EXPECTED_A_VALUES[coefficient][r]
            if coefficient == 1:
                assert a_value < 0
            else:
                assert a_value > 0
            emit(handle, f"field coefficient={coefficient} r={r} A={a_value:+d} dot={dot}")


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g315_n32_antipodal_live_ranks.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G315 n=32 antipodal live-rank audit")
        verify_model(handle)
        verify_large_field(handle)
        emit(
            handle,
            "PASS: at certified Proth-prime scale for n=32 and ranks 5,6, "
            "the exact field dot table matches the antipodal-pair model.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
