#!/usr/bin/env python3
"""Exact primitive depth-5 core census for #466 G91.

Enumerates endpoint multisets of size s on the dyadic subgroup mu_n in F_p.  For each
ordered pair of disjoint endpoint multisets with equal field sum it records both the
multiset-pair count and the number of ordered endpoint pairs represented by it.
No FFT or floating arithmetic enters the census.
"""
from __future__ import annotations

import argparse
import itertools
import math
from collections import defaultdict


def factor(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    return all(p % d for d in range(2, math.isqrt(p) + 1))


def primitive_root(p: int) -> int:
    assert is_prime(p), p
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def multinomial_weight(t: tuple[int, ...]) -> int:
    ans = math.factorial(len(t))
    for _, group in itertools.groupby(t):
        ans //= math.factorial(sum(1 for _ in group))
    return ans


def census(n: int, p: int, s: int) -> dict[str, int | float]:
    assert (p - 1) % n == 0
    g = primitive_root(p)
    z = pow(g, (p - 1) // n, p)
    assert pow(z, n, p) == 1 and (n == 1 or pow(z, n // 2, p) != 1)
    H = [pow(z, i, p) for i in range(n)]
    buckets: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    for t in itertools.combinations_with_replacement(range(n), s):
        mask = sum(1 << i for i in set(t))
        sm = sum(H[i] for i in t) % p
        buckets[sm].append((mask, multinomial_weight(t), len(set(t))))

    multiset_pairs = 0
    ordered_pairs = 0
    full_support_multiset_pairs = 0
    full_support_ordered_pairs = 0
    for bucket in buckets.values():
        for mask_l, wt_l, supp_l in bucket:
            for mask_r, wt_r, supp_r in bucket:
                if mask_l & mask_r:
                    continue
                multiset_pairs += 1
                ordered_pairs += wt_l * wt_r
                if supp_l == s and supp_r == s:
                    full_support_multiset_pairs += 1
                    full_support_ordered_pairs += wt_l * wt_r

    return {
        "n": n,
        "p": p,
        "s": s,
        "endpoint_multisets": math.comb(n + s - 1, s),
        "multiset_pairs": multiset_pairs,
        "ordered_pairs": ordered_pairs,
        "full_support_multiset_pairs": full_support_multiset_pairs,
        "full_support_ordered_pairs": full_support_ordered_pairs,
        "ordered_over_multiset": ordered_pairs / multiset_pairs if multiset_pairs else 0.0,
        "factorial_sq": math.factorial(s) ** 2,
        "ordered_orbits": ordered_pairs // n if ordered_pairs % n == 0 else -1,
        "multiset_orbits": multiset_pairs // n if multiset_pairs % n == 0 else -1,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", action="append", default=[], help="n,p pair")
    ap.add_argument("--depth", type=int, default=5)
    args = ap.parse_args()
    cells = [(8, 257), (16, 65537), (32, 1048609)]
    if args.cell:
        cells = [tuple(map(int, x.split(","))) for x in args.cell]
    for n, p in cells:
        row = census(n, p, args.depth)
        print(" ".join(f"{k}={v}" for k, v in row.items()))


if __name__ == "__main__":
    main()
