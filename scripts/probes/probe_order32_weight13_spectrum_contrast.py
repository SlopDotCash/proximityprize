#!/usr/bin/env python3
"""Contrast numbers: genuine (non-saturation) exceptions per rung.

Companion to ``probe_order32_weight13_spectrum.py``.  Reuses its ``fibers`` /
``target`` / ``is_prime`` helpers and prints, for h in {4, 8, 16}, how many primes
above the saturation threshold are genuinely deficient.  Stdlib only.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_order32_weight13_spectrum import fibers, target, is_prime  # noqa: E402


def main() -> None:
    for h in (4, 8, 16):
        T = target(h)
        m = 2 * h
        lim = 200000 if h == 16 else 50000
        rows = [
            (p, len(fibers(p, h)[1]))
            for p in range(m + 1, lim + 1)
            if p % m == 1 and is_prime(p)
        ]
        genuine = [(p, n) for p, n in rows if p > T]
        exc = [(p, n) for p, n in genuine if n != T]
        full = [p for p, n in genuine if n == T]
        print(
            f"h={h} (order {m}), |D|={T}, scan <= {lim}: {len(rows)} primes, "
            f"{len(genuine)} above saturation threshold, "
            f"{len(exc)} GENUINELY deficient, largest genuine exception "
            f"{max([p for p, _ in exc], default=None)}, "
            f"full at {len(full)} primes"
            f" (first full p = {min(full, default=None)})"
        )
        if 65537 <= lim:
            print(f"   p=65537 -> {len(fibers(65537, h)[1])} values (target {T})")


if __name__ == "__main__":
    main()
