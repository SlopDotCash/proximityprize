#!/usr/bin/env python3
"""#466 R307: depth-3 exact-Wick stress at binomial cyclotomic norm primes.

R305 identified the n=32 beta=4.872 exact-Wick violator

    p = (3^16 + 1) / 2,    zeta^5 == -3 (mod p),

as a divisor of the small-height norm Norm(3 + zeta).  This probe tests the same
mechanism at larger dyadic n: factor c^(n/2)+1, keep prime factors p == 1 mod n, and
evaluate the exact depth-3 excess by pushing the char-0 3-sum histogram modulo p.

The evaluator is bigint-safe: it uses sparse Python-integer evaluation of the shadow
vectors, so it can test norm factors far beyond int64 (for example the n=128 factor of
3^64+1, beta 14.348).
"""

from __future__ import annotations

import argparse
import math
import sys

import sympy as sp

from probe_r305_complete_census import build_n3


def order_n_element(p: int, n: int) -> int:
    for g in range(2, 1000):
        cand = pow(g, (p - 1) // n, p)
        if pow(cand, n // 2, p) != 1:
            return cand
    raise RuntimeError(f"no order-{n} element found quickly for p={p}")


def exact_excess_bigint(p: int, n: int, keys, cnts, e3_char0: int) -> int:
    m = n // 2
    g0 = order_n_element(p, n)
    powers = []
    x = 1
    for _ in range(m):
        powers.append(x)
        x = (x * g0) % p

    groups: dict[int, int] = {}
    for row, cnt in zip(keys, cnts):
        s = 0
        for j in row.nonzero()[0]:
            s += int(row[j]) * powers[int(j)]
        r = s % p
        groups[r] = groups.get(r, 0) + int(cnt)
    e3 = sum(v * v for v in groups.values())
    return e3 - e3_char0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True, help="dyadic order")
    ap.add_argument("--c-min", type=int, default=2)
    ap.add_argument("--c-max", type=int, default=7)
    args = ap.parse_args()

    n = args.n
    m = n // 2
    headroom = 45 * n * n - 40 * n
    wick = 15 * n**3

    keys, cnts = build_n3(n)
    e3_char0 = int((cnts**2).sum())
    print(
        f"n={n}: K={len(keys)} char0={e3_char0} "
        f"closed={15*n**3 - 45*n**2 + 40*n} headroom={headroom} wick={wick}",
        flush=True,
    )

    for c in range(args.c_min, args.c_max + 1):
        norm = c**m + 1
        factors = sp.factorint(norm)
        print(f"\nc={c}: factor c^(n/2)+1 ({norm.bit_length()} bits) = {factors}", flush=True)
        for p, exp in sorted(factors.items()):
            p = int(p)
            if p % n != 1:
                continue
            exc = exact_excess_bigint(p, n, keys, cnts, e3_char0)
            beta = math.log(p) / math.log(n)
            print(
                f"  p={p} exp={exp} beta={beta:.3f} excess={exc} "
                f"ratio={exc/headroom:.3f} E3/Wick={(e3_char0 + exc)/wick:.6f}"
                + ("  *** EXACT-WICK VIOLATION" if exc > headroom else ""),
                flush=True,
            )

    return 0


if __name__ == "__main__":
    sys.exit(main())
