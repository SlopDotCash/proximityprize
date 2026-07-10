#!/usr/bin/env python3
"""Exact census of fully distinct depth-five primitive-core scaling orbits.

For a dyadic multiplicative subgroup H of F_p^*, enumerate unordered pairs
{A,B} of disjoint five-subsets of H with equal sum in F_p, then quotient by
the diagonal H-scaling action using canonical representatives.

This is a falsification/structure probe, not a proof.  The coordinate S_5 x
S_5 and side-swap quotient is built into the use of unordered subset pairs.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict


def factor_distinct(n: int) -> list[int]:
    ans: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            ans.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ans.append(n)
    return ans


def primitive_root(p: int) -> int:
    factors = factor_distinct(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise ValueError(f"no primitive root modulo {p}")


def subgroup(p: int, n: int) -> tuple[int, ...]:
    if (p - 1) % n:
        raise ValueError(f"{n} does not divide p-1={p-1}")
    zeta = pow(primitive_root(p), (p - 1) // n, p)
    return tuple(sorted(pow(zeta, i, p) for i in range(n)))


def canonical_pair(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return (a, b) if a < b else (b, a)


def census(p: int, n: int) -> dict[str, int]:
    h = subgroup(p, n)
    buckets: dict[int, list[tuple[int, ...]]] = defaultdict(list)
    for a in itertools.combinations(h, 5):
        buckets[sum(a) % p].append(a)

    pairs = 0
    side_swap_fixed = 0
    for bucket in buckets.values():
        for i, a in enumerate(bucket):
            sa = set(a)
            for b in bucket[i + 1 :]:
                if sa.isdisjoint(b):
                    pairs += 1
                    if tuple(sorted((-x) % p for x in a)) == b:
                        side_swap_fixed += 1

    # An ordered five-set cannot be stabilized by a nonidentity element of a
    # 2-group: its induced permutation has order dividing both 5! and a power
    # of two, while every nontrivial orbit has even size and 5 is odd.  For an
    # unordered pair, the only remaining stabilizer swaps the sides.  Squaring
    # then fixes each side, so the multiplier is -1; these are exactly the
    # pairs B=-A recorded above.  Burnside therefore gives (pairs+fixed)/n.
    assert (pairs + side_swap_fixed) % n == 0
    orbits = (pairs + side_swap_fixed) // n

    return {
        "subsets": sum(len(v) for v in buckets.values()),
        "occupied_sums": len(buckets),
        "pairs": pairs,
        "side_swap_fixed": side_swap_fixed,
        "orbits": orbits,
        "crude_unordered_orbit_bound": n**8 // (2 * 120**2),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cell", action="append", default=[], help="n,p (repeatable)")
    args = parser.parse_args()
    cells = args.cell or ["8,97", "16,257", "16,1153", "32,1153"]
    for cell in cells:
        n, p = map(int, cell.split(","))
        row = census(p, n)
        ratio = row["orbits"] / row["crude_unordered_orbit_bound"] if row["crude_unordered_orbit_bound"] else 0
        print(f"n={n} p={p} " + " ".join(f"{k}={v}" for k, v in row.items()) + f" ratio={ratio:.12g}")


if __name__ == "__main__":
    main()
