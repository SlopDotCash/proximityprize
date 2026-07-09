#!/usr/bin/env python3
"""#466 R311: classify c=3 relation-web collision fibers by count signature.

R310 verifies the full delta histogram.  R311 refines it to the actual fiber-count
signatures, which are closer to a future Lean proof:

    (3n-3, 3, 1)  -> delta 24n-18, count n
    (6, 3, 3)     -> delta 90,     count 2n
    (6, 3)        -> delta 36,     count n(n-7)
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import sys

from probe_r305_complete_census import build_n3
from probe_r307_binomial_norm_depth3 import order_n_element


def signature_histogram(n: int, p: int) -> Counter[tuple[tuple[int, ...], int]]:
    keys, cnts = build_n3(n)
    g0 = order_n_element(p, n)
    powers = []
    x = 1
    for _ in range(n // 2):
        powers.append(x)
        x = (x * g0) % p

    groups: dict[int, list[int]] = defaultdict(list)
    for row, cnt in zip(keys, cnts):
        s = 0
        for j in row.nonzero()[0]:
            s += int(row[j]) * powers[int(j)]
        groups[s % p].append(int(cnt))

    hist: Counter[tuple[tuple[int, ...], int]] = Counter()
    for counts in groups.values():
        if len(counts) <= 1:
            continue
        total = sum(counts)
        self_mass = sum(c * c for c in counts)
        delta = total * total - self_mass
        if delta:
            hist[(tuple(sorted(counts, reverse=True)), delta)] += 1
    return hist


def predicted_signature_histogram(n: int) -> Counter[tuple[tuple[int, ...], int]]:
    return Counter({
        ((3 * n - 3, 3, 1), 24 * n - 18): n,
        ((6, 3, 3), 90): 2 * n,
        ((6, 3), 36): n * (n - 7),
    })


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    args = ap.parse_args()

    observed = signature_histogram(args.n, args.p)
    predicted = predicted_signature_histogram(args.n)

    print(f"n={args.n} p={args.p}")
    print("observed signature histogram:")
    for (sig, delta), count in sorted(observed.items(), key=lambda x: (-x[0][1], x[0][0])):
        print(f"  signature={sig} delta={delta} count={count} mass={delta * count}")
    print("predicted signature histogram:")
    for (sig, delta), count in sorted(predicted.items(), key=lambda x: (-x[0][1], x[0][0])):
        print(f"  signature={sig} delta={delta} count={count} mass={delta * count}")
    print(f"matches predicted signatures: {observed == predicted}")
    return 0 if observed == predicted else 1


if __name__ == "__main__":
    sys.exit(main())
