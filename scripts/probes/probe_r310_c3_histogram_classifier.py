#!/usr/bin/env python3
"""#466 R310: classify the full c=3 relation-web histogram.

R308 found, for n=64 and n=128, that the dangerous c=3 binomial-norm primes have
three positive collision-delta strata:

    delta = 24n - 18   with count n
    delta = 90         with count 2n
    delta = 36         with count n(n-7)

R309 proved that this histogram implies excess = 60n^2 - 90n, hence violates
the exact-Wick headroom.  This probe is the executable classifier for the still-open
combinatorial input: given a prime p and a primitive n-th root g with some g^d = 3,
compute the full R305 pushforward collision histogram and compare it to the predicted
three-stratum form.
"""

from __future__ import annotations

import argparse
from collections import Counter
import math
import sys

from probe_r305_complete_census import build_n3
from probe_r307_binomial_norm_depth3 import order_n_element


def find_constant_exponent(p: int, n: int, g0: int, c: int) -> int | None:
    x = 1
    for j in range(n):
        if x == c % p:
            return j
        x = (x * g0) % p
    return None


def classify(n: int, p: int, c: int = 3) -> tuple[Counter[int], int, int | None]:
    keys, cnts = build_n3(n)
    e3_char0 = int((cnts**2).sum())
    g0 = order_n_element(p, n)
    d = find_constant_exponent(p, n, g0, c)

    powers = []
    x = 1
    for _ in range(n // 2):
        powers.append(x)
        x = (x * g0) % p

    groups: dict[int, list[int]] = {}
    for row, cnt in zip(keys, cnts):
        s = 0
        for j in row.nonzero()[0]:
            s += int(row[j]) * powers[int(j)]
        groups.setdefault(s % p, []).append(int(cnt))

    hist: Counter[int] = Counter()
    excess = 0
    for counts in groups.values():
        if len(counts) <= 1:
            continue
        total = sum(counts)
        self_mass = sum(x * x for x in counts)
        delta = total * total - self_mass
        if delta:
            hist[delta] += 1
            excess += delta
    assert excess == sum(delta * count for delta, count in hist.items())
    # e3_char0 is intentionally returned only through the assertion path above; keeping it here
    # catches accidental future rewrites where build_n3 is not actually used.
    assert e3_char0 == 15 * n**3 - 45 * n**2 + 40 * n
    return hist, excess, d


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--c", type=int, default=3)
    args = ap.parse_args()

    n = args.n
    p = args.p
    hist, excess, d = classify(n, p, args.c)
    predicted = Counter({
        24 * n - 18: n,
        90: 2 * n,
        36: n * (n - 7),
    })
    predicted_excess = 60 * n * n - 90 * n
    headroom = 45 * n * n - 40 * n

    print(f"n={n} p={p} beta={math.log(p)/math.log(n):.3f} c={args.c} d={d}", flush=True)
    print("observed histogram:")
    for delta, count in sorted(hist.items(), reverse=True):
        print(f"  delta={delta} count={count} mass={delta * count}")
    print("predicted histogram:")
    for delta, count in sorted(predicted.items(), reverse=True):
        print(f"  delta={delta} count={count} mass={delta * count}")
    print(f"observed excess={excess}")
    print(f"predicted excess={predicted_excess}")
    print(f"headroom={headroom}")
    print(f"matches predicted histogram: {hist == predicted}")
    print(f"violates exact-Wick headroom: {excess > headroom}")
    return 0 if hist == predicted else 1


if __name__ == "__main__":
    sys.exit(main())
