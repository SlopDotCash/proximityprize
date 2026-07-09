#!/usr/bin/env python3
"""#466 R310: exhaustive scan of the max-frequency law B^2 / (n ln p).

r309 found census-bad primes at n=16 sit at B^2/(n ln p) = 1.12-1.15 vs <=1.03 for clean
ones (B = max_{b!=0} |eta_b|, eta = subgroup Gauss periods).  This probe scans EVERY prime
p ≡ 1 (mod n) in [lo, hi], computing the exact ratio, to decide:
  (a) is the strong-form law  B^2 <= C * n * ln p  (C ~ 1.2)  violated anywhere?
  (b) is the bad/clean separation a dichotomy or a continuum?
Reports the full ratio histogram, the top ratios, and any prime exceeding --c-bound.
"""

from __future__ import annotations

import argparse
import math
import sys

import numpy as np


def sieve(lo: int, hi: int, mod: int) -> list[int]:
    is_p = np.ones(hi + 1, dtype=bool)
    is_p[:2] = False
    for i in range(2, int(hi**0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = False
    ps = np.nonzero(is_p)[0]
    return [int(p) for p in ps if p >= lo and p % mod == 1]


def factor(x: int) -> set[int]:
    fs, d = set(), 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d)
            x //= d
        d += 1
    if x > 1:
        fs.add(x)
    return fs


def prim_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError


def max_freq_sq(p: int, n: int) -> float:
    g = prim_root(p)
    gm = pow(g, (p - 1) // n, p)
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] = 1.0
        x = x * gm % p
    eta = np.fft.fft(ind)
    m2 = eta.real**2 + eta.imag**2
    return float(np.max(m2[1:]))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--min-p", type=int, required=True)
    ap.add_argument("--max-p", type=int, required=True)
    ap.add_argument("--c-bound", type=float, default=1.2)
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--progress-every", type=int, default=500)
    args = ap.parse_args()

    n = args.n
    primes = sieve(args.min_p, args.max_p, n)
    print(f"R310 n={n}: {len(primes)} primes in [{args.min_p}, {args.max_p}]; "
          f"testing B^2 <= {args.c_bound} * n * ln p", flush=True)

    ratios = []
    worst: list[tuple[float, int]] = []
    violations = 0
    for i, p in enumerate(primes):
        b2 = max_freq_sq(p, n)
        ratio = b2 / (n * math.log(p))
        ratios.append(ratio)
        worst.append((ratio, p))
        worst.sort(reverse=True)
        del worst[args.top :]
        if ratio > args.c_bound:
            violations += 1
            print(f"*** LAW VIOLATION p={p} ratio={ratio:.4f}", flush=True)
        if (i + 1) % args.progress_every == 0:
            print(f"progress {i+1}/{len(primes)} p={p} max={worst[0][0]:.4f} "
                  f"violations={violations}", flush=True)

    arr = np.array(ratios)
    print(f"\nscan complete: {len(primes)} primes, violations(>{args.c_bound})={violations}")
    print(f"ratio stats: min={arr.min():.4f} mean={arr.mean():.4f} "
          f"median={np.median(arr):.4f} p99={np.percentile(arr,99):.4f} max={arr.max():.4f}")
    hist, edges = np.histogram(arr, bins=20)
    for h, e0, e1 in zip(hist, edges[:-1], edges[1:]):
        print(f"  [{e0:.3f},{e1:.3f}): {h}")
    print("\ntop ratios:")
    for ratio, p in worst:
        print(f"  p={p:>10} beta={math.log(p)/math.log(n):.3f} ratio={ratio:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
