#!/usr/bin/env python3
"""#466 R305b: fast EXACT depth-3 excess scanner for n = 2^k via char-0 grouping.

excess(p, n) = E3(p,n) - E3^char0(n) = sum_{c in F_p} rep3(c)^2 - sum_w N3(w)^2

where the char-0 3-sum histogram N3 (over exact vectors in Z^(n/2), basis zeta^j,
Phi_n = x^(n/2)+1) is computed ONCE, and per prime we only group the K distinct vectors
by their evaluation w(g) mod p (g = element of order n).  O(K log K) per prime, exact
integer arithmetic throughout.  Scans every prime p ≡ 1 (mod n) in [lo, hi] and reports
all primes with nonzero excess, flagging exact-Wick violations (excess > 45n^2 - 40n).
"""

from __future__ import annotations

import argparse
import math
import sys
from collections import defaultdict

import numpy as np


def sieve_primes(lo: int, hi: int, mod: int) -> list[int]:
    is_p = np.ones(hi + 1, dtype=bool)
    is_p[:2] = False
    for i in range(2, int(hi**0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = False
    ps = np.nonzero(is_p)[0]
    return [int(p) for p in ps if p >= lo and p % mod == 1]


def order_n_element(p: int, n: int) -> int:
    # find g0 of exact order n mod p (n = 2^k, p ≡ 1 mod n)
    for g in range(2, p):
        g0 = pow(g, (p - 1) // n, p)
        if pow(g0, n // 2, p) != 1:
            return g0
    raise RuntimeError


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=32)
    ap.add_argument("--min-p", type=int, required=True)
    ap.add_argument("--max-p", type=int, required=True)
    ap.add_argument("--progress-every", type=int, default=5000)
    args = ap.parse_args()

    n = args.n
    m = n // 2
    headroom = 45 * n**2 - 40 * n

    # char-0 3-sum histogram
    N3: dict[tuple[int, ...], int] = defaultdict(int)
    for a in range(n):
        sa, ia = (1, a) if a < m else (-1, a - m)
        for b in range(n):
            sb, ib = (1, b) if b < m else (-1, b - m)
            for c in range(n):
                sc, ic = (1, c) if c < m else (-1, c - m)
                v = [0] * m
                v[ia] += sa
                v[ib] += sb
                v[ic] += sc
                N3[tuple(v)] += 1
    keys = np.array(list(N3.keys()), dtype=np.int64)  # K x m
    cnts = np.array([N3[tuple(k)] for k in keys], dtype=np.int64)
    K = len(keys)
    e3_char0 = int(np.sum(cnts * cnts))
    assert e3_char0 == 15 * n**3 - 45 * n**2 + 40 * n
    print(f"n={n}: K={K} vectors, char-0 E3={e3_char0}, headroom={headroom}", flush=True)

    primes = sieve_primes(args.min_p, args.max_p, n)
    print(f"scanning {len(primes)} primes ≡ 1 mod {n} in [{args.min_p}, {args.max_p}]",
          flush=True)

    bad = 0
    violations = 0
    for i, p in enumerate(primes):
        g0 = order_n_element(p, n)
        powers = np.empty(m, dtype=np.int64)
        x = 1
        for j in range(m):
            powers[j] = x
            x = x * g0 % p
        evals = (keys @ powers) % p  # exact: |keys| <= 3, powers < p < 2^63/48 safe
        order = np.argsort(evals, kind="stable")
        ev_sorted = evals[order]
        ct_sorted = cnts[order]
        # group-sum squares
        boundaries = np.nonzero(np.diff(ev_sorted))[0] + 1
        group_sums = np.add.reduceat(ct_sorted, np.concatenate(([0], boundaries)))
        e3p = int(np.sum(group_sums.astype(np.int64) ** 2))
        excess = e3p - e3_char0
        if excess:
            bad += 1
            beta = math.log(p) / math.log(n)
            viol = excess > headroom
            violations += viol
            print(f"badprime p={p} beta={beta:.3f} excess={excess}"
                  + ("  *** EXACT-WICK VIOLATION" if viol else ""), flush=True)
        if (i + 1) % args.progress_every == 0:
            print(f"progress {i+1}/{len(primes)} p={p} bad={bad} violations={violations}",
                  flush=True)

    print(f"\nscan complete: {len(primes)} primes, nonzero-excess={bad}, "
          f"exact-Wick violations={violations}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
