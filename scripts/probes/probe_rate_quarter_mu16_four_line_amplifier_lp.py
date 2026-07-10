#!/usr/bin/env python3
"""Exact rational LP for four-line universal mu_16 common-factor amplifiers.

The fixed three-line universal cell has 29 universal split-cubic fourth-line
extensions (cross-prime census).  For each extension, this program optimizes
the lifted ownership allocation over the 16 quotient fibres, allowing:

* one received equality class per non-hole coordinate;
* isolated holes, worth four labels;
* all-four/dead coordinates;
* at most one fibre-unit of extra all-four roots from a common factor
  (`deg G < m`, normalized here as `sum g <= 1`).

The bad-label constraint is `proper + 4*holes >= 16`; core sizes of all four
lines are maximized in the minimum.  SymPy's rational simplex keeps the
answer exact.  This is an asymptotic/fractional optimizer; a prize-scale
integer construction still needs rounding and explicit finite-field labels.
"""

from __future__ import annotations

import sys
from pathlib import Path

from sympy import Eq, Rational, symbols
from sympy.solvers.simplex import lpmax

sys.path.insert(0, str(Path(__file__).resolve().parent))
from probe_rate_quarter_mu16_universal_four_extensions import PRIMES, census


FIXED = {
    (0, 1): (0, 1, 8),
    (0, 2): (3, 5, 7),
    (1, 2): (2, 9, 10),
}


def components(record, exponent):
    edges = dict(FIXED)
    edges[(0, 3)], edges[(1, 3)], edges[(2, 3)] = record
    parent = list(range(4))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[b] = a

    for (a, b), roots in edges.items():
        if exponent in roots:
            union(a, b)
    groups = {}
    for i in range(4):
        groups.setdefault(find(i), []).append(i)
    return tuple(sorted(tuple(v) for v in groups.values()))


def optimize(record):
    constraints = []
    owner_vars = []
    holes = []
    common = []
    core_terms = [[] for _ in range(4)]
    proper = []
    dead = []

    for e in range(16):
        parts = components(record, e)
        xs = symbols(f"x{e}_0:{len(parts)}")
        h = symbols(f"h{e}")
        g = symbols(f"g{e}")
        holes.append(h)
        common.append(g)
        local = list(xs) + [h, g]
        constraints += [v >= 0 for v in local]
        constraints.append(Eq(sum(local), 1))
        for x, part in zip(xs, parts):
            owner_vars.append(x)
            if len(part) == 4:
                dead.append(x)
            else:
                proper.append(x)
            for i in part:
                core_terms[i].append(x)
        dead.append(g)
        for i in range(4):
            core_terms[i].append(g)

    z = symbols("z")
    constraints.append(z >= 0)
    constraints.append(sum(common) <= 1)
    constraints.append(sum(proper) + 4 * sum(holes) >= 16)
    for i in range(4):
        constraints.append(sum(core_terms[i]) >= z)

    optimum, solution = lpmax(z, constraints)
    return optimum, solution, {
        "holes": sum(solution.get(v, 0) for v in holes),
        "common_factor_roots": sum(solution.get(v, 0) for v in common),
        "dead": sum(solution.get(v, 0) for v in dead),
        "proper": sum(solution.get(v, 0) for v in proper),
        "cores": tuple(sum(solution.get(v, 0) for v in core_terms[i]) for i in range(4)),
        "patterns": tuple(components(record, e) for e in range(16)),
    }


def main() -> None:
    records = set.intersection(*(census(p) for p in PRIMES))
    results = []
    for idx, record in enumerate(sorted(records)):
        optimum, _solution, data = optimize(record)
        results.append((optimum, record, data))
        print("candidate", idx + 1, "/", len(records), "opt", optimum)
    results.sort(key=lambda x: x[0], reverse=True)
    print({
        "candidate_count": len(results),
        "best": [
            {
                "min_core_over_m": str(opt),
                "agreement_density": str(opt / 16),
                "radius": str(1 - opt / 16),
                "record": record,
                "ledger": {k: str(v) for k, v in data.items() if k != "patterns"},
                "patterns": data["patterns"],
            }
            for opt, record, data in results[:5]
        ],
    })


if __name__ == "__main__":
    main()
