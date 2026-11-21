#!/usr/bin/env python3
"""G312 exact scale audit for G278's integer-carry localization no-go.

G278 showed on small/medium cells that the adjacent-rank CORE alignment does
not localize cleanly into carry zero or nonzero carry buckets. This probe
reproduces the published p=433,n=16 carry cells and then runs the same carry
decomposition at the certified Proth prime

    p = 111*2^128 + 1.

For n=16 and r in {5,6} at this large field, all mass lies in carry 0. This is
a finite toy-order scale audit only: it says the small-field carry obstruction
is scale-sensitive here, not that the production n=2^30 problem is solved.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from math import ceil, comb, floor
from pathlib import Path
from tempfile import gettempdir


N = 16
SMALL_P = 433
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1
RANKS = (5, 6)


def require(condition: bool, message: str) -> None:
    """Keep the G312 carry-census checks active under Python optimization."""
    if not condition:
        raise AssertionError(message)


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
    require(x == 1 and len(set(out)) == n, f"subgroup construction failed for p={p}, n={n}")
    return sorted(out)


def subgroup_small(p: int, n: int) -> list[int]:
    return subgroup_from_root(p, n, primitive_root(p))


def certify_proth_prime() -> int:
    require(PROTH_K % 2 == 1, "Proth multiplier must be odd")
    require(PROTH_K < (1 << PROTH_M), "Proth multiplier exceeds the Proth bound")
    # Proth theorem: this congruence proves PROTH_P is prime.
    require(
        pow(PROTH_WITNESS, (PROTH_P - 1) // 2, PROTH_P) == PROTH_P - 1,
        "Proth primality witness failed",
    )
    return PROTH_P


def subgroup_proth(n: int) -> list[int]:
    p = certify_proth_prime()
    require(n <= (1 << PROTH_M), f"subgroup order n={n} exceeds the Proth 2-adic scale")
    return subgroup_from_root(p, n, PROTH_WITNESS)


def subset_integer_sums(group: list[int], r: int) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for indices in combinations(range(len(group)), r):
        out[sum(group[i] for i in indices)] += 1
    require(
        sum(out.values()) == comb(len(group), r),
        f"integer subset-sum census lost mass at rank r={r}",
    )
    return dict(out)


def subset_mod_sums(group: list[int], p: int, r: int) -> list[int]:
    out: list[int] = []
    for indices in combinations(range(len(group)), r):
        total = 0
        for i in indices:
            total = (total + group[i]) % p
        out.append(total)
    require(len(out) == comb(len(group), r), f"modular subset enumeration count changed at r={r}")
    return out


def integer_kernel(group: list[int]) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for y in group:
        for z in group:
            out[2 * y - z] += 1
    require(sum(out.values()) == len(group) ** 2, "integer kernel lost mass")
    return dict(out)


def modular_kernel(group: list[int], p: int) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for y in group:
        for z in group:
            out[(2 * y - z) % p] += 1
    require(sum(out.values()) == len(group) ** 2, "modular kernel lost mass")
    return dict(out)


def diff_count(left: dict[int, int], right: dict[int, int], d: int) -> int:
    # Count pairs with left_sum - right_sum = d.
    if len(left) <= len(right):
        return sum(value * right.get(s - d, 0) for s, value in left.items())
    return sum(value * left.get(t + d, 0) for t, value in right.items())


def carry_census(group: list[int], p: int, r: int) -> dict[str, object]:
    n = len(group)
    left = subset_integer_sums(group, r)
    right = subset_integer_sums(group, r - 1)
    dmin = min(left) - max(right)
    dmax = max(left) - min(right)
    carries: defaultdict[int, int] = defaultdict(int)
    cache: dict[int, int] = {}

    for d1, weight in integer_kernel(group).items():
        # 2*y + sum(B) - z - sum(A) = k*p, so sum(A)-sum(B) = d1 - k*p.
        klo = floor((d1 - dmax) / p) - 1
        khi = ceil((d1 - dmin) / p) + 1
        for k in range(klo, khi + 1):
            d = d1 - k * p
            if d < dmin or d > dmax:
                continue
            if d not in cache:
                cache[d] = diff_count(left, right, d)
            if cache[d]:
                carries[k] += weight * cache[d]

    carries = defaultdict(int, {k: v for k, v in sorted(carries.items()) if v})
    total = comb(n, r) * comb(n, r - 1)
    j_total = sum(carries.values())
    gate = p * j_total - n * n * total
    need = n * n * total // p + 1
    return {
        "carries": dict(carries),
        "J": j_total,
        "gate": gate,
        "need": need,
        "J0": carries.get(0, 0),
        "Enz": j_total - carries.get(0, 0),
        "total": total,
    }


def direct_modular_alignment(group: list[int], p: int, r: int) -> int:
    left = subset_mod_sums(group, p, r)
    right = subset_mod_sums(group, p, r - 1)
    kernel = modular_kernel(group, p)
    dot = 0
    for x in left:
        for y in right:
            dot += kernel.get((x - y) % p, 0)
    return dot


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_small(handle) -> None:
    group = subgroup_small(SMALL_P, N)
    expected = {
        5: {
            "gate": 3_425_440,
            "J": 4_708_000,
            "need": 4_700_090,
            "carries": {-3: 1185, -2: 105117, -1: 1057270, 0: 2380856,
                        1: 1057270, 2: 105117, 3: 1185},
        },
        6: {
            "gate": 52_032,
            "J": 20_680_512,
            "need": 20_680_392,
            "carries": {-3: 8741, -2: 531582, -1: 4773523, 0: 10052820,
                        1: 4773523, 2: 531582, 3: 8741},
        },
    }
    emit(handle, "reproducing G278 small cell p=433 n=16")
    for r in RANKS:
        row = carry_census(group, SMALL_P, r)
        require(
            row["gate"] == expected[r]["gate"],
            f"G312 small exact gate pin failed at r={r}: {row['gate']}",
        )
        require(row["J"] == expected[r]["J"], f"G312 small total-mass pin failed at r={r}")
        require(row["need"] == expected[r]["need"], f"G312 small threshold pin failed at r={r}")
        require(
            row["carries"] == expected[r]["carries"],
            f"G312 small carry census pin failed at r={r}: {row['carries']}",
        )
        require(row["J0"] < row["need"], f"G312 small carry-zero bucket reached threshold at r={r}")
        require(row["Enz"] < row["need"], f"G312 small nonzero buckets reached threshold at r={r}")
        emit(
            handle,
            f"small p={SMALL_P} n={N} r={r} A={row['gate']:+d} "
            f"J={row['J']} need={row['need']} carries={row['carries']}",
        )


def verify_large(handle) -> None:
    p = certify_proth_prime()
    group = subgroup_proth(N)
    expected = {
        5: (321_216, 12_132_759_625_789_254_812_263_498_506_989_117_214_991_787_712),
        6: (1_064_448, 40_205_630_224_372_760_716_789_501_328_599_919_806_465_162_752),
    }
    require(p > N * (1 << 128), "certified Proth prime is below the advertised scale")
    emit(handle, f"large Proth prime p={p}=111*2^128+1 witness={PROTH_WITNESS}")
    for r in RANKS:
        row = carry_census(group, p, r)
        direct_j = direct_modular_alignment(group, p, r)
        require(row["J"] == direct_j, f"G312 carry total disagrees with direct modular count at r={r}")
        require(
            row["J"] == expected[r][0],
            f"G312 large total-mass pin failed at r={r}: {row['J']}",
        )
        require(row["gate"] == expected[r][1], f"G312 large gate pin failed at r={r}")
        require(row["need"] == 1, f"G312 large threshold changed at r={r}: {row['need']}")
        require(
            row["carries"] == {0: expected[r][0]},
            f"G312 large carry-zero census pin failed at r={r}: {row['carries']}",
        )
        require(
            row["J0"] == row["J"] and row["Enz"] == 0,
            f"G312 large mass is not wholly in carry zero at r={r}",
        )
        emit(
            handle,
            f"large p={p} n={N} r={r} A={row['gate']:+d} "
            f"J={row['J']} need={row['need']} carries={row['carries']}",
        )


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g312_carry_scale_audit.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G312 carry scale audit")
        verify_small(handle)
        verify_large(handle)
        emit(
            handle,
            "PASS: the small-field spread-carry obstruction flips at certified "
            "large field size for n=16; all checked large-cell mass is carry 0.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
