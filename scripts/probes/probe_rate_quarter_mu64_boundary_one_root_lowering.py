#!/usr/bin/env python3
"""Exhaust one-root lowering of lifted mu_16 quartic locator triangles.

Every disjoint quartic locator triangle on mu_16 lifts through X->X^4 to a
disjoint degree-16 triangle on mu_64.  The primitive direction can only use
degree 15.  This probe removes one of the 16 roots from each lifted locator
and tests whether the three resulting monic degree-15 locators are still
affinely collinear.  All 16^3 removals are checked for every boundary
triangle, then survivors are intersected across split primes.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from probe_rate_quarter_locator_degree_lowering import (
    affine_parameter,
    boundary_hits,
    locator,
    primitive_root,
)


PRIMES = (193, 257, 449)


def lifted(block):
    return tuple(sorted(e + 16 * j for e in block for j in range(4)))


def census(p: int, triangles):
    omega = pow(primitive_root(p), (p - 1) // 64, p)
    mu = tuple(pow(omega, e, p) for e in range(64))
    records = set()
    tested = 0
    for tidx, blocks in enumerate(triangles):
        lifts = tuple(lifted(block) for block in blocks)
        lowered = []
        for roots in lifts:
            lowered.append({
                removed: locator(mu, tuple(e for e in roots if e != removed), p)
                for removed in roots
            })
        for ra, fa in lowered[0].items():
            for rb, fb in lowered[1].items():
                for rc, fc in lowered[2].items():
                    tested += 1
                    if affine_parameter(fa, fb, fc, p) is not None:
                        records.add((tidx, ra, rb, rc))
    return records, tested


def main() -> None:
    # The 72 quartic boundary triangles are universal; intersect once more
    # across two mu_16 split primes to keep that premise executable.
    triangles193 = boundary_hits(193)
    triangles257 = set(boundary_hits(257))
    triangles = [x for x in triangles193 if x in triangles257]
    outputs = {p: census(p, triangles) for p in PRIMES}
    common = set.intersection(*(x[0] for x in outputs.values()))
    print({
        "universal_boundary_triangles": len(triangles),
        "per_prime": {
            p: {"tested": tested, "hits": len(hits)}
            for p, (hits, tested) in outputs.items()
        },
        "cross_prime_hits": len(common),
        "first_hits": sorted(common)[:30],
        "hit_triangles": sorted({x[0] for x in common}),
    })


if __name__ == "__main__":
    main()
