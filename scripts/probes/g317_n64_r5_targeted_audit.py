#!/usr/bin/env python3
"""G317 targeted n=64, rank-5 finite-field audit.

G316 gives the antipodal-model formula. A full n=64, rank-6 finite-field
histogram is too large for a safe Python dict probe, but rank 5 is feasible.
This script checks the next larger toy order at the certified Proth prime

    p = 111*2^128 + 1.

It uses the subgroup-scaling identity

    sum_t W_a(t) R(t) = n * sum_{u in G} R(a-u),

where u=z/y and R is invariant under G-dilation. This queries 64 quotient
shifts instead of materializing the full weighted kernel. At n=64,r=5, the
finite-field dots match the antipodal-model predictions exactly:

    coefficient 1: dot = 0
    coefficient 2: dot = 864230400.

This is still a finite toy-order audit, not a production n=2^30 theorem.
"""
from __future__ import annotations

from collections import defaultdict
from math import comb
from pathlib import Path
from tempfile import gettempdir


N = 64
RANK = 5
COEFFICIENTS = (1, 2)
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1

EXPECTED_HIST_SIZES = {
    0: 1,
    1: 64,
    2: 1985,
    3: 39_744,
    4: 577_345,
    5: 6_483_776,
}

EXPECTED_DOTS = {
    1: 0,
    2: 864_230_400,
}

EXPECTED_A = {
    1: -19_842_793_211_953_152,
    2: 32_643_142_634_550_265_248_631_476_078_696_581_721_630_936_603_648,
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
            prev = list(dp[r - 1].items())
            row = dp[r]
            for s, value in prev:
                row[(s + x) % p] += value
    for r in range(max_r + 1):
        assert len(dp[r]) == EXPECTED_HIST_SIZES[r]
        assert sum(dp[r].values()) == comb(len(group), r)
    return [dict(row) for row in dp]


def row_value(left: dict[int, int], right: dict[int, int], p: int, t: int) -> int:
    # R(t) = sum_x left[x] * right[x - t].
    if len(left) <= len(right):
        return sum(value * right.get((x - t) % p, 0) for x, value in left.items())
    return sum(value * left.get((y + t) % p, 0) for y, value in right.items())


def quotient_weighted_dot(group: list[int], dp: list[dict[int, int]], p: int, coefficient: int) -> int:
    total = 0
    nonzero_shift_count = 0
    for u in group:
        value = row_value(dp[RANK], dp[RANK - 1], p, (coefficient - u) % p)
        if value:
            nonzero_shift_count += 1
        total += len(group) * value
    if coefficient == 1:
        assert nonzero_shift_count == 0
    else:
        assert nonzero_shift_count == 63
    return total


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_large_field(handle) -> None:
    p = certify_proth_prime()
    assert p > N * (1 << 128)
    group = subgroup_proth(N)
    dp = subset_hist_sparse(group, p, RANK)
    total_pairs = comb(N, RANK) * comb(N, RANK - 1)

    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    for r in range(RANK + 1):
        emit(handle, f"hist r={r} support={len(dp[r])} mass={sum(dp[r].values())}")
    for coefficient in COEFFICIENTS:
        dot = quotient_weighted_dot(group, dp, p, coefficient)
        a_value = p * dot - N * N * total_pairs
        assert dot == EXPECTED_DOTS[coefficient]
        assert a_value == EXPECTED_A[coefficient]
        if coefficient == 1:
            assert a_value < 0
        else:
            assert a_value > 0
        emit(handle, f"coefficient={coefficient} r={RANK} A={a_value:+d} dot={dot}")


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g317_n64_r5_targeted_audit.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G317 n=64 rank-5 targeted finite-field audit")
        verify_large_field(handle)
        emit(
            handle,
            "PASS: at certified Proth-prime scale for n=64,r=5, the exact "
            "finite-field dot table matches the antipodal-model prediction.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
