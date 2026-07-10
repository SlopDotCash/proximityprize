#!/usr/bin/env python3
"""Cross-prime mu_16 split-cubic clique graph and exact ownership LP.

The fixed universal triangle is

    0, (1-lambda)L_A, L_C.

The companion four-extension census finds 29 fourth lines surviving four test
primes.  This program reconstructs each line over every test prime, joins two
extensions when their difference is a split cubic with the *same exponent root
triple* at all four primes, and enumerates maximal cliques in the resulting
compatibility graph.  A clique of s extensions gives L=3+s mutually
split-cubic lines in this cross-prime survivor census.  The census is evidence
for characteristic-independent structure, not an algebraic universality proof.

For each clique it solves the exact rational common-factor/ownership LP over
the sixteen quotient fibres.  At each fibre one may:

* assign the received row to one polynomial-value component (one safe label
  unless that component contains all L lines);
* make a hole (worth the number of distinct value components at that fibre,
  not blindly L labels);
* spend common-locator roots, which join all lines and are dead.

The common-root budget is at most one fibre unit (the asymptotic normalization
deg(G)<=m), the scalar budget is at least 16, and the objective maximizes the
minimum of the L core sizes.  SymPy's simplex keeps every optimum rational.

By default only maximal compatibility cliques are optimized.  Pass ``--all``
to optimize every clique with at least two extensions, which checks all
L>=5 subcliques as well.
"""

from __future__ import annotations

import sys
import ast
import subprocess
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from probe_rate_quarter_mu16_universal_four_extensions import (
    PRIMES,
    census,
    locator,
    primitive_root,
    scale,
    sub,
)


def prime_data(p: int, records):
    z = pow(primitive_root(p), (p - 1) // 16, p)
    mu = tuple(pow(z, e, p) for e in range(16))
    triples = tuple(combinations(range(16), 3))
    locators = {roots: locator(mu, roots, p) for roots in triples}
    split = {
        scale(s, polynomial, p): roots
        for roots, polynomial in locators.items()
        for s in range(1, p)
    }

    roots_a, roots_b, roots_c = (0, 1, 8), (2, 9, 10), (3, 5, 7)
    pa, pb, pc = locators[roots_a], locators[roots_b], locators[roots_c]
    pivot = next(j for j in range(3) if pa[j] != pb[j])
    lam = (
        (pc[pivot] - pa[pivot])
        * pow((pb[pivot] - pa[pivot]) % p, p - 2, p)
        % p
    )
    line_a = scale(1 - lam, pa, p)
    line_b = pc
    zero = (0,) * 4

    polynomials = {}
    for record in records:
        roots_c0, roots_ca, roots_cb = record
        hits = []
        for s in range(1, p):
            candidate = scale(s, locators[roots_c0], p)
            if (
                split.get(sub(candidate, line_a, p)) == roots_ca
                and split.get(sub(candidate, line_b, p)) == roots_cb
            ):
                hits.append(candidate)
        assert len(hits) == 1, (p, record, len(hits))
        polynomials[record] = hits[0]

    return {
        "mu": mu,
        "split": split,
        "polynomials": polynomials,
        "fixed": (zero, line_a, line_b),
    }


def compatibility_graph(records, data):
    adjacency = {i: set() for i in range(len(records))}
    edge_roots = {}
    for i, j in combinations(range(len(records)), 2):
        roots_by_prime = []
        for p in PRIMES:
            pi = data[p]["polynomials"][records[i]]
            pj = data[p]["polynomials"][records[j]]
            roots = data[p]["split"].get(sub(pi, pj, p))
            if roots is None:
                break
            roots_by_prime.append(roots)
        if len(roots_by_prime) != len(PRIMES):
            continue
        # A characteristic-dependent change of exponent roots is not treated
        # as a candidate-universal edge.
        if len(set(roots_by_prime)) != 1:
            continue
        adjacency[i].add(j)
        adjacency[j].add(i)
        edge_roots[(i, j)] = roots_by_prime[0]
    return adjacency, edge_roots


def maximal_cliques(adjacency):
    result = []

    def bron_kerbosch(chosen, possible, excluded):
        if not possible and not excluded:
            result.append(tuple(sorted(chosen)))
            return
        pivot = max(
            possible | excluded,
            key=lambda v: len(possible & adjacency[v]),
        ) if possible or excluded else None
        candidates = possible - (adjacency[pivot] if pivot is not None else set())
        for vertex in sorted(candidates):
            bron_kerbosch(
                chosen | {vertex},
                possible & adjacency[vertex],
                excluded & adjacency[vertex],
            )
            possible.remove(vertex)
            excluded.add(vertex)

    bron_kerbosch(set(), set(adjacency), set())
    return sorted(set(result), key=lambda clique: (len(clique), clique))


def all_cliques(adjacency):
    result = []

    def extend(prefix, candidates):
        for position, vertex in enumerate(candidates):
            clique = prefix + (vertex,)
            result.append(clique)
            extend(
                clique,
                [
                    other
                    for other in candidates[position + 1 :]
                    if other in adjacency[vertex]
                ],
            )

    extend((), list(sorted(adjacency)))
    return result


def eval_poly(polynomial, x, p):
    out = 0
    for coefficient in reversed(polynomial):
        out = (out * x + coefficient) % p
    return out


def partitions_for_clique(clique, records, data, p=97):
    fs = data[p]["fixed"] + tuple(
        data[p]["polynomials"][records[i]] for i in clique
    )
    rows = []
    for x in data[p]["mu"]:
        buckets = {}
        for i, polynomial in enumerate(fs):
            buckets.setdefault(eval_poly(polynomial, x, p), []).append(i)
        rows.append(tuple(sorted(tuple(bucket) for bucket in buckets.values())))
    return tuple(rows)


def optimize_exact(parts, tag):
    # Imported lazily so the lightweight driver can launch each memory-heavy
    # exact simplex solve in a child without itself retaining SymPy caches.
    from sympy import Eq, symbols
    from sympy.solvers.simplex import lpmin

    line_count = max(i for row in parts for bucket in row for i in bucket) + 1
    weights = symbols(f"w{tag}_0:{line_count}")
    label_price = symbols(f"mu{tag}")
    common_price = symbols(f"nu{tag}")
    fibre_bounds = symbols(f"y{tag}_0:16")
    constraints = [weight >= 0 for weight in weights]
    constraints += [label_price >= 0, common_price >= 0]
    constraints += [bound >= 0 for bound in fibre_bounds]
    constraints.append(Eq(sum(weights), 1))

    # Exact dual of the ownership LP.  For fixed core weights, label price,
    # and common-root price, each fibre takes the largest value among its
    # owner components, a hole, and a new common root.
    for exponent, row in enumerate(parts):
        constraints.append(
            fibre_bounds[exponent] >= len(row) * label_price
        )
        constraints.append(fibre_bounds[exponent] >= 1 - common_price)
        for component in row:
            owner_label = 0 if len(component) == line_count else label_price
            constraints.append(
                fibre_bounds[exponent] >=
                    sum(weights[i] for i in component) + owner_label
            )

    objective = sum(fibre_bounds) - 16 * label_price + common_price
    optimum, solution = lpmin(objective, constraints)
    value = lambda variable: solution.get(variable, 0)
    return optimum, {
        "line_count": line_count,
        "dual_core_weights": tuple(value(weight) for weight in weights),
        "dual_label_price": value(label_price),
        "dual_common_price": value(common_price),
        "dual_fibre_bounds": tuple(value(bound) for bound in fibre_bounds),
    }


def main() -> None:
    records = sorted(set.intersection(*(census(p) for p in PRIMES)))
    data = {p: prime_data(p, records) for p in PRIMES}
    adjacency, edge_roots = compatibility_graph(records, data)
    maximal = maximal_cliques(adjacency)
    every = all_cliques(adjacency)
    if "--worker" in sys.argv[1:]:
        position = sys.argv.index("--worker")
        clique = tuple(int(v) for v in sys.argv[position + 1].split(",") if v)
        parts = partitions_for_clique(clique, records, data)
        optimum, ledger = optimize_exact(parts, "_worker")
        print((str(optimum), {key: str(value) for key, value in ledger.items()}))
        return
    use_all = "--all" in sys.argv[1:]
    selected = [
        clique
        for clique in (every if use_all else maximal)
        if len(clique) >= 2
    ]
    original_selected_count = len(selected)
    start = int(sys.argv[sys.argv.index("--start") + 1]) \
        if "--start" in sys.argv[1:] else 0
    stop = int(sys.argv[sys.argv.index("--stop") + 1]) \
        if "--stop" in sys.argv[1:] else original_selected_count
    selected = selected[start:stop]

    results = []
    for index, clique in enumerate(selected):
        parts = partitions_for_clique(clique, records, data)
        # SymPy's simplex retains enough global expression cache to grow
        # across dozens of LPs.  Run each exact solve in a fresh process so
        # the census is reproducible under modest memory limits.
        worker = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "--worker",
                ",".join(map(str, clique)),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        optimum_string, ledger_strings = ast.literal_eval(
            worker.stdout.strip().splitlines()[-1]
        )
        optimum = Fraction(optimum_string)
        ledger = {
            key: (int(value) if key == "line_count" else value)
            for key, value in ledger_strings.items()
        }
        results.append((optimum, clique, ledger, parts))
        print(
            "optimized",
            index + 1,
            "/",
            len(selected),
            "L=",
            ledger["line_count"],
            "z=",
            optimum,
            flush=True,
        )

    by_lines = defaultdict(list)
    for result in results:
        by_lines[result[2]["line_count"]].append(result)
    summary = {}
    for line_count, group in sorted(by_lines.items()):
        group.sort(key=lambda item: item[0], reverse=True)
        optimum, clique, ledger, parts = group[0]
        summary[line_count] = {
            "tested_cliques": len(group),
            "best_min_core_over_m": str(optimum),
            "agreement_density": str(optimum / 16),
            "radius": str(1 - optimum / 16),
            "extension_vertices": clique,
            "extension_records": tuple(records[i] for i in clique),
            "ledger": {key: str(value) for key, value in ledger.items()},
            "patterns": parts,
        }

    print({
        "primes": PRIMES,
        "vertex_count": len(records),
        "edge_count": len(edge_roots),
        "degree_sequence": sorted(
            (len(adjacency[i]) for i in adjacency), reverse=True
        ),
        "maximal_clique_count": len(maximal),
        "maximal_extension_clique_sizes": dict(Counter(map(len, maximal))),
        "largest_extension_clique": max(maximal, key=len),
        "largest_total_line_count": 3 + max(map(len, maximal)),
        "all_clique_sizes": dict(Counter(map(len, every))),
        "optimized_scope": "all_cliques" if use_all else "maximal_cliques",
        "optimized_slice": (start, stop),
        "full_scope_clique_count": original_selected_count,
        "results_by_line_count": summary,
        "three_line_target_min_core_over_m": "53/6",
        "any_strict_improvement": any(
            optimum > Fraction(53, 6)
            for optimum, _clique, _ledger, _parts in results
        ),
    })


if __name__ == "__main__":
    main()
