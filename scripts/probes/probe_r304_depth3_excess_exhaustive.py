#!/usr/bin/env python3
"""#466 R304: exhaustive adversarial stress of the r53 depth-3 headroom atom.

The r53 reduction closes the r=3 rung iff the wraparound excess
    excess(p, n) = E3(p, n) - (15 n^3 - 45 n^2 + 40 n)
stays <= 45 n^2 - 40 n for every prime p ≡ 1 (mod n) with p >= n^3 (beta >= 3),
i.e. iff E3 <= 15 n^3 (exact Wick, (2r-1)!! = 15 at r=3).

r52 established bad primes with POSITIVE excess exist (universal vanishing refuted) but
only probed a narrow frontier. This probe scans EVERY prime p ≡ 1 (mod n), n^3 <= p <= bound,
computing E3 exactly via FFT (q*E3 = sum_b |eta_b|^6, eta = DFT of the mu_n indicator),
and reports any violation of the atom — a single violating prime REFUTES the r53 route.
"""

from __future__ import annotations

import argparse
import math
import sys

import numpy as np


def sieve_primes(limit: int) -> np.ndarray:
    is_p = np.ones(limit + 1, dtype=bool)
    is_p[:2] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = False
    return np.nonzero(is_p)[0]


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
    raise RuntimeError(f"no primitive root for {p}")


def e3_fft(p: int, n: int) -> int:
    """E3 = (1/p) * sum_b |eta_b|^6, eta = DFT_p of the mu_n indicator (exact integer)."""
    g = prim_root(p)
    gm = pow(g, (p - 1) // n, p)
    ind = np.zeros(p, dtype=np.float64)
    x = 1
    for _ in range(n):
        ind[x] = 1.0
        x = x * gm % p
    eta = np.fft.fft(ind)
    m2 = eta.real * eta.real + eta.imag * eta.imag
    total = float(np.sum(m2 * m2 * m2))
    e3 = total / p
    return int(round(e3))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--max-p", type=int, required=True)
    ap.add_argument("--min-p", type=int, default=0, help="default n^3 (beta >= 3)")
    ap.add_argument("--progress-every", type=int, default=200)
    ap.add_argument("--top", type=int, default=12)
    args = ap.parse_args()

    n = args.n
    lo = args.min_p if args.min_p else n**3
    hi = args.max_p
    char0 = 15 * n**3 - 45 * n**2 + 40 * n
    wick = 15 * n**3
    headroom = 45 * n**2 - 40 * n

    primes = [int(p) for p in sieve_primes(hi) if p >= lo and p % n == 1]
    print(
        f"R304 n={n} window p in [{lo}, {hi}] (beta in "
        f"[{math.log(lo)/math.log(n):.2f}, {math.log(hi)/math.log(n):.2f}]): "
        f"{len(primes)} primes ≡ 1 mod {n}; atom: excess <= {headroom} (E3 <= {wick})",
        flush=True,
    )

    worst: list[tuple[int, int, int]] = []  # (excess, p, e3)
    violations = 0
    for i, p in enumerate(primes):
        e3 = e3_fft(p, n)
        excess = e3 - char0
        worst.append((excess, p, e3))
        worst.sort(reverse=True)
        del worst[args.top :]
        if excess > headroom:
            violations += 1
            print(
                f"*** VIOLATION p={p} beta={math.log(p)/math.log(n):.3f} "
                f"E3={e3} excess={excess} > headroom={headroom}",
                flush=True,
            )
        if (i + 1) % args.progress_every == 0:
            print(
                f"progress {i+1}/{len(primes)} p={p} "
                f"worstExcess={worst[0][0]} (p={worst[0][1]}) violations={violations}",
                flush=True,
            )

    print(f"\nscan complete: {len(primes)} primes, violations={violations}")
    print(f"atom 'excess <= {headroom}': {'REFUTED' if violations else 'SURVIVES this window'}")
    print("\ntop excess primes:")
    for excess, p, e3 in worst:
        print(
            f"  p={p:>9} beta={math.log(p)/math.log(n):.3f} E3={e3:>12} "
            f"excess={excess:>8} excess/headroom={excess/headroom:+.4f} E3/Wick={e3/wick:.4f}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
