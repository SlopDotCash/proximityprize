#!/usr/bin/env python3
"""#466 R313: sample normalized vector templates inside the c=3 relation web.

R311 classified collision fibers by count signatures.  This probe normalizes each
positive collision fiber by translating the largest-count vector to index 0 in the signed
dyadic basis.  It then reports how many normalized vector templates occur for each
signature/delta class.

The output is intended as proof-search scaffolding: it exposes the finite parameter families
that a Lean proof of `C3RelationWebSignature21` should enumerate.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import sys

from probe_r305_complete_census import build_n3
from probe_r307_binomial_norm_depth3 import order_n_element


def sparse(row) -> dict[int, int]:
    return {int(i): int(row[i]) for i in row.nonzero()[0]}


def shift_vec(vec: dict[int, int], shift: int, n: int) -> tuple[tuple[int, int], ...]:
    m = n // 2
    out: Counter[int] = Counter()
    for j, coeff in vec.items():
        k = (j - shift) % n
        if k >= m:
            out[k - m] -= coeff
        else:
            out[k] += coeff
    return tuple(sorted((i, v) for i, v in out.items() if v))


def base_index(fiber: list[tuple[int, int, dict[int, int]]]) -> int:
    _, _, vec = max(fiber, key=lambda item: item[1])
    if len(vec) == 1:
        return next(iter(vec.keys()))
    return min(vec.keys())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--top", type=int, default=10)
    args = ap.parse_args()

    n = args.n
    p = args.p
    keys, cnts = build_n3(n)
    g0 = order_n_element(p, n)
    powers = []
    x = 1
    for _ in range(n // 2):
        powers.append(x)
        x = (x * g0) % p

    groups: dict[int, list[tuple[int, int, dict[int, int]]]] = defaultdict(list)
    for idx, (row, cnt) in enumerate(zip(keys, cnts)):
        value = 0
        for j in row.nonzero()[0]:
            value += int(row[j]) * powers[int(j)]
        groups[value % p].append((idx, int(cnt), sparse(row)))

    templates: dict[tuple[tuple[int, ...], int], Counter[tuple[tuple[int, tuple[tuple[int, int], ...]], ...]]] = (
        defaultdict(Counter)
    )
    for fiber in groups.values():
        counts = [cnt for _, cnt, _ in fiber]
        if len(counts) <= 1:
            continue
        total = sum(counts)
        self_mass = sum(cnt * cnt for cnt in counts)
        delta = total * total - self_mass
        if not delta:
            continue
        signature = tuple(sorted(counts, reverse=True))
        base = base_index(fiber)
        template = tuple(
            sorted([(cnt, shift_vec(vec, base, n)) for _, cnt, vec in fiber], reverse=True)
        )
        templates[(signature, delta)][template] += 1

    print(f"n={n} p={p}")
    for key in sorted(templates.keys(), key=lambda item: (-item[1], item[0])):
        counter = templates[key]
        print(f"\nsignature={key[0]} delta={key[1]} template_count={len(counter)}")
        for template, count in counter.most_common(args.top):
            print(f"  count={count} template={template}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
