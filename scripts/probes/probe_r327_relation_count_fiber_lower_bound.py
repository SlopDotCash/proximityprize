#!/usr/bin/env python3
"""#466 R327: exact pigeonhole lower bound for realized shadow relations.

The Lean theorem gives

    choose(m, r) <= q * (D + 1),

where n=2m, q is the field cardinality, and D is the cardinality of
shadowKernelRelations.  This probe evaluates the resulting integer lower bound

    D >= ceil(choose(m,r) / q) - 1

at the power-of-two proxy q=n*2^128 and at the global q<2^256 cap.  All
combinatorial integers are computed exactly; only the displayed logarithms are
floating-point summaries.
"""

from __future__ import annotations

import math


def forced_relation_lower_bound(m: int, r: int, q: int) -> int:
    endpoint_count = math.comb(m, r)
    return (endpoint_count + q - 1) // q - 1


def report(mu: int, q_bits: int) -> None:
    n = 1 << mu
    m = n // 2
    q = 1 << q_bits
    r = math.ceil(math.log(q))
    endpoints = math.comb(m, r)
    lower = forced_relation_lower_bound(m, r, q)
    assert q * (lower + 1) >= endpoints
    if lower > 0:
        assert q * lower < endpoints
    print(
        f"mu={mu:2d} q=2^{q_bits:3d} r={r:3d} "
        f"log2_choose={math.log2(endpoints):10.6f} "
        f"log2_forced_D={math.log2(lower):10.6f} "
        f"log2_effective_base={math.log2(lower)/r:9.6f}"
    )


def main() -> int:
    print("# R327 exact relation-count pigeonhole pressure")
    for mu in (20, 25, 30):
        report(mu, mu + 128)
    print("# Largest prize length against the global field-cardinality cap")
    report(30, 256)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
