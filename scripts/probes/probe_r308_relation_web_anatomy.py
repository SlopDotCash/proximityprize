#!/usr/bin/env python3
"""#466 R308: inspect relation-web collision anatomy for depth-3 binomial norm primes.

R307 showed that some small-height binomial norm factors create very high-beta exact-Wick
violations, while other binomial norm factors are harmless.  This probe prints the actual
collision fibers in the R305 char-zero shadow pushforward, so the dangerous invariant can be
studied as a relation-web mass rather than a raw prime.
"""

from __future__ import annotations

import argparse
from collections import Counter
import math
import sys

from probe_r305_complete_census import build_n3
from probe_r307_binomial_norm_depth3 import order_n_element


def sparse(row) -> dict[int, int]:
    return {int(i): int(row[i]) for i in row.nonzero()[0]}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--top", type=int, default=16)
    ap.add_argument("--constants", type=str, default="2,3,4,5")
    args = ap.parse_args()

    n = args.n
    p = args.p
    keys, cnts = build_n3(n)
    e3_char0 = int((cnts**2).sum())
    headroom = 45 * n * n - 40 * n
    wick = 15 * n**3
    g0 = order_n_element(p, n)

    powers = []
    x = 1
    for _ in range(n):
        powers.append(x)
        x = (x * g0) % p

    constants = [int(t) for t in args.constants.split(",") if t]
    hits = []
    for c in constants:
        inv = pow(c, -1, p)
        targets = {c % p: f"{c}", (-c) % p: f"-{c}",
                   inv: f"{c}^-1", (-inv) % p: f"-{c}^-1"}
        for j, val in enumerate(powers):
            if val in targets:
                hits.append((j, targets[val], val))

    groups: dict[int, list[tuple[int, int]]] = {}
    half = n // 2
    for idx, (row, cnt) in enumerate(zip(keys, cnts)):
        s = 0
        for j in row.nonzero()[0]:
            # rows live in the signed basis 0..half-1.
            s += int(row[j]) * powers[int(j)]
        r = s % p
        groups.setdefault(r, []).append((idx, int(cnt)))

    rows = []
    delta_hist: Counter[int] = Counter()
    excess = 0
    for r, lst in groups.items():
        if len(lst) <= 1:
            continue
        total = sum(c for _, c in lst)
        self_mass = sum(c * c for _, c in lst)
        delta = total * total - self_mass
        if delta:
            rows.append((delta, total, self_mass, r, lst))
            delta_hist[delta] += 1
            excess += delta
    rows.sort(reverse=True)

    print(
        f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} "
        f"K={len(keys)} g0={g0}",
        flush=True,
    )
    print(f"constant hits among powers of g0: {hits}", flush=True)
    print(
        f"char0={e3_char0} headroom={headroom} wick={wick} "
        f"excess={excess} ratio={excess/headroom:.6f} "
        f"E3/Wick={(e3_char0 + excess)/wick:.6f}"
        + ("  *** EXACT-WICK VIOLATION" if excess > headroom else ""),
        flush=True,
    )
    print(f"collision residues with positive delta: {len(rows)}", flush=True)
    print("delta histogram:", flush=True)
    for delta, multiplicity in sorted(delta_hist.items(), reverse=True):
        print(f"  delta={delta} count={multiplicity} mass={delta * multiplicity}", flush=True)
    formula = 60 * n * n - 90 * n
    if excess == formula:
        print(f"matches c=3 formula excess = 60*n^2 - 90*n = {formula}", flush=True)

    for rank, (delta, total, self_mass, residue, lst) in enumerate(rows[: args.top], start=1):
        print(
            f"\n#{rank}: delta={delta} total={total} self={self_mass} "
            f"fiber_size={len(lst)} residue={residue}",
            flush=True,
        )
        for idx, cnt in sorted(lst, key=lambda t: (-t[1], t[0]))[:8]:
            print(f"  cnt={cnt:>4} vec={sparse(keys[idx])}", flush=True)

    return 0


if __name__ == "__main__":
    sys.exit(main())
