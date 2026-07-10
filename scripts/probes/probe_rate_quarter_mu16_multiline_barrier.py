#!/usr/bin/env python3
"""Reproducible certificates for the mu_16 multi-line amplifier barrier.

There are two complementary audits.

``--fixed-triangle`` (the default) starts with the known universal triangle,
intersects its fourth-line extensions over four split primes, constructs the
extension compatibility graph, enumerates every clique, and solves the
fractional ownership LP for total line counts 3 through 8.  Every reported
optimum is checked twice with ``fractions.Fraction``: once by an exact primal
solution and once by an exact dual solution of the same value.

``--global-triangles`` normalizes one nonzero pair difference and checks all
nine affine/Galois orbits of three-subsets of Z/16.  It verifies that no
nonproportional triangle surviving all four primes has LP value above 53/6.

``--global-four-orbit I`` performs the analogous exhaustive four-line audit
for one of the nine normalized first-difference orbits.  Running I=0,...,8
covers every non-collinear four-line clique under this finite-prime census.
The mode is split by orbit to keep memory and runtime bounded.

``--global-five-orbit I`` adds a second mutually compatible extension to
each normalized triangle and performs the corresponding five-line audit.

The cross-prime intersection is deliberately described as a census, not as
a characteristic-zero proof: it is a computable superset test for universal
cyclotomic identities.  The fixed-triangle LP certificates themselves are
exact once their finite list of root records is supplied.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, permutations

import numpy as np
from scipy.optimize import linprog


PRIMES = (97, 193, 257, 353)
ORDER = 16
DEGREE = 3
ORBIT_REPRESENTATIVES = (
    (0, 1, 2),
    (0, 1, 3),
    (0, 1, 4),
    (0, 1, 7),
    (0, 1, 8),
    (0, 2, 4),
    (0, 2, 6),
    (0, 2, 8),
    (0, 4, 8),
)

FIXED_ROOTS = {
    (0, 1): (0, 1, 8),
    (0, 2): (3, 5, 7),
    (1, 2): (2, 9, 10),
}

_MASK_MAP_CACHE = {}


def primitive_root(p: int) -> int:
    factors = []
    n = p - 1
    q = 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return next(
        g
        for g in range(2, p)
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors)
    )


def sub(a: tuple[int, ...], b: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple((x - y) % p for x, y in zip(a, b))


def scale(s: int, a: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple(s * x % p for x in a)


def mul(a: tuple[int, ...], b: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return tuple(out)


def locator(
    mu: tuple[int, ...], roots: tuple[int, ...], p: int
) -> tuple[int, ...]:
    out = (1,)
    for e in roots:
        out = mul(out, ((-mu[e]) % p, 1), p)
    return out


def field_data(p: int):
    zeta = pow(primitive_root(p), (p - 1) // ORDER, p)
    mu = tuple(pow(zeta, e, p) for e in range(ORDER))
    triples = tuple(combinations(range(ORDER), DEGREE))
    locators = {roots: locator(mu, roots, p) for roots in triples}
    split = {
        scale(s, polynomial, p): roots
        for roots, polynomial in locators.items()
        for s in range(1, p)
    }
    return locators, split


def equality_partitions(
    line_count: int,
    edge_roots: dict[tuple[int, int], tuple[int, ...]],
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    result = []
    for exponent in range(ORDER):
        parent = list(range(line_count))

        def find(x: int) -> int:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for (i, j), roots in edge_roots.items():
            if exponent in roots:
                a, b = find(i), find(j)
                if a != b:
                    parent[b] = a
        groups: dict[int, list[int]] = {}
        for i in range(line_count):
            groups.setdefault(find(i), []).append(i)
        result.append(tuple(sorted(tuple(group) for group in groups.values())))
    return tuple(result)


def rationalize(value: float) -> Fraction:
    if abs(value) < 1e-8:
        return Fraction(0)
    return Fraction(float(value)).limit_denominator(1_000_000)


def exact_primal(partitions):
    line_count = max(
        i for row in partitions for part in row for i in part
    ) + 1
    variables = []
    for exponent, row in enumerate(partitions):
        variables.extend((exponent, "owner", part) for part in row)
        variables.extend(((exponent, "hole", ()), (exponent, "common", ())))

    z_index = len(variables)
    dimension = z_index + 1
    objective = np.zeros(dimension)
    objective[z_index] = -1

    equalities = []
    equality_rhs = []
    for exponent in range(ORDER):
        row = np.zeros(dimension)
        for j, (source, _kind, _part) in enumerate(variables):
            if source == exponent:
                row[j] = 1
        equalities.append(row)
        equality_rhs.append(1)

    inequalities = []
    inequality_rhs = []
    common = np.zeros(dimension)
    for j, (_source, kind, _part) in enumerate(variables):
        if kind == "common":
            common[j] = 1
    inequalities.append(common)
    inequality_rhs.append(1)

    bad = np.zeros(dimension)
    for j, (_source, kind, part) in enumerate(variables):
        if kind == "hole":
            bad[j] = -line_count
        elif kind == "owner" and len(part) < line_count:
            bad[j] = -1
    inequalities.append(bad)
    inequality_rhs.append(-ORDER)

    for line in range(line_count):
        core = np.zeros(dimension)
        core[z_index] = 1
        for j, (_source, kind, part) in enumerate(variables):
            if kind == "common" or (kind == "owner" and line in part):
                core[j] = -1
        inequalities.append(core)
        inequality_rhs.append(0)

    result = linprog(
        objective,
        A_ub=inequalities,
        b_ub=inequality_rhs,
        A_eq=equalities,
        b_eq=equality_rhs,
        bounds=(0, None),
        method="highs",
    )
    assert result.success, result.message
    solution = tuple(rationalize(x) for x in result.x)
    allocation, optimum = solution[:-1], solution[-1]
    assert all(x >= 0 for x in solution)
    for exponent in range(ORDER):
        assert sum(
            allocation[j]
            for j, (source, _kind, _part) in enumerate(variables)
            if source == exponent
        ) == 1
    assert sum(
        allocation[j]
        for j, (_source, kind, _part) in enumerate(variables)
        if kind == "common"
    ) <= 1
    assert sum(
        (line_count if kind == "hole" else
         1 if kind == "owner" and len(part) < line_count else 0)
        * allocation[j]
        for j, (_source, kind, part) in enumerate(variables)
    ) >= ORDER
    cores = tuple(
        sum(
            allocation[j]
            for j, (_source, kind, part) in enumerate(variables)
            if kind == "common" or (kind == "owner" and line in part)
        )
        for line in range(line_count)
    )
    assert min(cores) >= optimum
    return optimum, cores


def exact_dual(partitions):
    """Return and exactly verify a dual upper certificate.

    The variables are line weights ``w_i``, a common-factor multiplier
    ``alpha``, a bad-label multiplier ``beta``, and one local envelope
    ``lambda_e`` per quotient fibre.  Weak duality gives

        z <= sum(lambda_e) + alpha - 16*beta.
    """

    line_count = max(
        i for row in partitions for part in row for i in part
    ) + 1
    alpha_index = line_count
    beta_index = line_count + 1
    lambda_start = line_count + 2
    dimension = lambda_start + ORDER
    objective = np.zeros(dimension)
    objective[alpha_index] = 1
    objective[beta_index] = -ORDER
    objective[lambda_start:] = 1

    inequalities = []
    rhs = []
    for exponent, row_parts in enumerate(partitions):
        for part in row_parts:
            row = np.zeros(dimension)
            for line in part:
                row[line] = 1
            if len(part) < line_count:
                row[beta_index] = 1
            row[lambda_start + exponent] = -1
            inequalities.append(row)
            rhs.append(0)
        hole = np.zeros(dimension)
        hole[beta_index] = line_count
        hole[lambda_start + exponent] = -1
        inequalities.append(hole)
        rhs.append(0)
        common = np.zeros(dimension)
        common[alpha_index] = -1
        common[lambda_start + exponent] = -1
        inequalities.append(common)
        rhs.append(-1)

    equality = np.zeros((1, dimension))
    equality[0, :line_count] = 1
    result = linprog(
        objective,
        A_ub=inequalities,
        b_ub=rhs,
        A_eq=equality,
        b_eq=[1],
        bounds=(0, None),
        method="highs",
    )
    assert result.success, result.message
    solution = tuple(rationalize(x) for x in result.x)
    weights = solution[:line_count]
    alpha = solution[alpha_index]
    beta = solution[beta_index]
    lambdas = solution[lambda_start:]
    assert all(x >= 0 for x in solution)
    assert sum(weights) == 1
    for exponent, row_parts in enumerate(partitions):
        for part in row_parts:
            proper_cost = beta if len(part) < line_count else 0
            assert sum(weights[i] for i in part) + proper_cost <= lambdas[exponent]
        assert line_count * beta <= lambdas[exponent]
        assert 1 - alpha <= lambdas[exponent]
    optimum = sum(lambdas) + alpha - ORDER * beta
    return optimum, (weights, alpha, beta, lambdas)


def exact_optimum(partitions):
    lower, primal = exact_primal(partitions)
    upper, dual = exact_dual(partitions)
    assert lower == upper, (lower, upper)
    return lower, primal, dual


def fixed_triangle_data(data):
    root_a, root_b, root_c = (0, 1, 8), (2, 9, 10), (3, 5, 7)
    maps = {}
    survivor_sets = []
    per_prime_counts = {}
    for p in PRIMES:
        locators, split = data[p]
        pa, pb, pc = locators[root_a], locators[root_b], locators[root_c]
        pivot = next(j for j in range(DEGREE) if pa[j] != pb[j])
        lam = (
            (pc[pivot] - pa[pivot])
            * pow((pb[pivot] - pa[pivot]) % p, p - 2, p)
            % p
        )
        a = scale(1 - lam, pa, p)
        b = pc
        candidates = {}
        for c, roots_c in split.items():
            ca, cb = sub(c, a, p), sub(c, b, p)
            if c not in {a, b} and ca in split and cb in split:
                candidates[(roots_c, split[ca], split[cb])] = c
        maps[p] = (split, candidates)
        survivor_sets.append(set(candidates))
        per_prime_counts[p] = len(candidates)

    vertices = set.intersection(*survivor_sets)
    adjacency = {vertex: set() for vertex in vertices}
    edge_roots = {}
    for u, v in combinations(sorted(vertices), 2):
        roots = []
        for p in PRIMES:
            split, candidates = maps[p]
            difference = sub(candidates[u], candidates[v], p)
            if difference not in split:
                break
            roots.append(split[difference])
        else:
            if len(set(roots)) == 1:
                adjacency[u].add(v)
                adjacency[v].add(u)
                edge_roots[(u, v)] = roots[0]
    return per_prime_counts, vertices, adjacency, edge_roots


def all_cliques(vertices, adjacency):
    cliques = [()]
    for vertex in sorted(vertices):
        cliques.extend(
            (*clique, vertex)
            for clique in tuple(cliques)
            if all(vertex in adjacency[u] for u in clique)
        )
    return cliques


def fixed_clique_partitions(clique, extension_edge_roots):
    edges = dict(FIXED_ROOTS)
    for j, record in enumerate(clique, 3):
        edges[(0, j)], edges[(1, j)], edges[(2, j)] = record
    for i, u in enumerate(clique):
        for j, v in enumerate(clique[i + 1 :], i + 1):
            edges[(i + 3, j + 3)] = extension_edge_roots[
                tuple(sorted((u, v)))
            ]
    return equality_partitions(3 + len(clique), edges)


def run_fixed(data):
    counts, vertices, adjacency, edge_roots = fixed_triangle_data(data)
    cliques = all_cliques(vertices, adjacency)
    histogram = {}
    best = {}
    for clique in cliques:
        line_count = 3 + len(clique)
        histogram[len(clique)] = histogram.get(len(clique), 0) + 1
        partitions = fixed_clique_partitions(clique, edge_roots)
        optimum, primal, dual = exact_optimum(partitions)
        if line_count not in best or optimum > best[line_count][0]:
            best[line_count] = (optimum, clique, primal, dual)

    summary = {}
    for line_count, (optimum, clique, primal, dual) in sorted(best.items()):
        weights, alpha, beta, lambdas = dual
        summary[line_count] = {
            "min_core_over_m": str(optimum),
            "radius": str(1 - optimum / ORDER),
            "extension_count": len(clique),
            "clique": clique,
            "primal_cores": tuple(map(str, primal)),
            "dual_weights": tuple(map(str, weights)),
            "dual_alpha": str(alpha),
            "dual_beta": str(beta),
            "dual_lambda_histogram": {
                str(value): lambdas.count(value) for value in sorted(set(lambdas))
            },
        }
    collinear = {}
    for line_count in range(3, 9):
        collinear_edges = {
            edge: (0, 1, 8)
            for edge in combinations(range(line_count), 2)
        }
        partitions = equality_partitions(line_count, collinear_edges)
        optimum, _primal, _dual = exact_optimum(partitions)
        collinear[line_count] = str(optimum)
    print({
        "mode": "fixed_triangle",
        "per_prime_extension_counts": counts,
        "universal_extensions": len(vertices),
        "compatibility_edges": sum(map(len, adjacency.values())) // 2,
        "extension_clique_histogram": histogram,
        "best_by_total_line_count": summary,
        "all_collinear_pencil_by_total_line_count": collinear,
    })


def normalized_neighbors(first_roots, data):
    neighbors = {}
    records = {}
    for p in PRIMES:
        locators, split = data[p]
        first = locators[first_roots]
        neighbors[p] = []
        records[p] = {}
        for polynomial, roots in split.items():
            if polynomial == first:
                continue
            difference = sub(polynomial, first, p)
            if difference in split:
                record = (roots, split[difference])
                neighbors[p].append((polynomial, *record))
                records[p].setdefault(record, []).append(polynomial)
    return neighbors, records


def raw_compact_signature(partitions):
    return tuple(sorted(
        tuple(sorted(sum(1 << i for i in part) for part in row))
        for row in partitions
    ))


def canonicalize_signature(rows, line_count):
    if line_count not in _MASK_MAP_CACHE:
        _MASK_MAP_CACHE[line_count] = tuple(
            tuple(
                sum(
                    1 << permutation[i]
                    for i in range(line_count)
                    if mask & (1 << i)
                )
                for mask in range(1 << line_count)
            )
            for permutation in permutations(range(line_count))
        )
    best = None
    for mask_map in _MASK_MAP_CACHE[line_count]:
        transformed = tuple(sorted(
            tuple(sorted(
                mask_map[mask]
                for mask in row
            ))
            for row in rows
        ))
        if best is None or transformed < best:
            best = transformed
    return best


def compact_signature(partitions, line_count):
    return canonicalize_signature(raw_compact_signature(partitions), line_count)


def decode_signature(signature, line_count):
    return tuple(
        tuple(
            tuple(i for i in range(line_count) if mask & (1 << i))
            for mask in row
        )
        for row in signature
    )


def universal_triangle_records(first_roots, records):
    return set.intersection(*(set(records[p]) for p in PRIMES)) - {
        (first_roots, first_roots)
    }


def run_global_triangles(data):
    signatures = {}
    orbit_counts = {}
    for first_roots in ORBIT_REPRESENTATIVES:
        _neighbors, records = normalized_neighbors(first_roots, data)
        triangles = universal_triangle_records(first_roots, records)
        orbit_counts[first_roots] = len(triangles)
        for record in triangles:
            edges = {
                (0, 1): first_roots,
                (0, 2): record[0],
                (1, 2): record[1],
            }
            partitions = equality_partitions(3, edges)
            signature = compact_signature(partitions, 3)
            signatures.setdefault(signature, (first_roots, record))

    bounds = {
        signature: exact_dual(decode_signature(signature, 3))[0]
        for signature in signatures
    }
    maximum = max(bounds.values())
    print({
        "mode": "global_triangles",
        "primes": PRIMES,
        "orbit_triangle_counts": orbit_counts,
        "total_normalized_nonproportional_records": sum(orbit_counts.values()),
        "partition_signatures": len(signatures),
        "largest_exact_dual_upper": str(maximum),
        "three_line_value": "53/6",
        "beats_three_line_value": maximum > Fraction(53, 6),
        "maximizing_example": signatures[
            next(signature for signature, value in bounds.items() if value == maximum)
        ],
    })


def run_global_four_orbit(data, orbit_index):
    first_roots = ORBIT_REPRESENTATIVES[orbit_index]
    neighbors, records = normalized_neighbors(first_roots, data)
    triangles = universal_triangle_records(first_roots, records)
    signatures = {}
    canonical_cache = {}
    extension_count = 0
    for triangle in triangles:
        base = {p: records[p][triangle][0] for p in PRIMES}
        extension_sets = []
        for p in PRIMES:
            _locators, split = data[p]
            extensions = set()
            for polynomial, roots_0, roots_1 in neighbors[p]:
                if polynomial == base[p]:
                    continue
                difference = sub(polynomial, base[p], p)
                if difference in split:
                    extensions.add((roots_0, roots_1, split[difference]))
            extension_sets.append(extensions)
        extensions = set.intersection(*extension_sets)
        extension_count += len(extensions)
        for extension in extensions:
            edges = {
                (0, 1): first_roots,
                (0, 2): triangle[0],
                (1, 2): triangle[1],
                (0, 3): extension[0],
                (1, 3): extension[1],
                (2, 3): extension[2],
            }
            partitions = equality_partitions(4, edges)
            raw_signature = raw_compact_signature(partitions)
            if raw_signature not in canonical_cache:
                canonical_cache[raw_signature] = canonicalize_signature(
                    raw_signature, 4
                )
            signature = canonical_cache[raw_signature]
            signatures.setdefault(signature, (triangle, extension))

    bounds = {
        signature: exact_dual(decode_signature(signature, 4))[0]
        for signature in signatures
    }
    maximum = max(bounds.values())
    print({
        "mode": "global_four_orbit",
        "orbit_index": orbit_index,
        "first_root_orbit_representative": first_roots,
        "primes": PRIMES,
        "normalized_nonproportional_triangles": len(triangles),
        "universal_four_line_records_with_multiplicity": extension_count,
        "raw_partition_signatures": len(canonical_cache),
        "partition_signatures": len(signatures),
        "largest_exact_dual_upper": str(maximum),
        "three_line_value": "53/6",
        "beats_three_line_value": maximum > Fraction(53, 6),
        "maximizing_example": signatures[
            next(signature for signature, value in bounds.items() if value == maximum)
        ],
    })


def run_global_five_orbit(data, orbit_index):
    first_roots = ORBIT_REPRESENTATIVES[orbit_index]
    neighbors, records = normalized_neighbors(first_roots, data)
    triangles = universal_triangle_records(first_roots, records)
    signatures = {}
    canonical_cache = {}
    extension_pair_count = 0
    for triangle in triangles:
        base = {p: records[p][triangle][0] for p in PRIMES}
        extension_maps = {}
        extension_sets = []
        for p in PRIMES:
            _locators, split = data[p]
            extension_map = {}
            for polynomial, roots_0, roots_1 in neighbors[p]:
                if polynomial == base[p]:
                    continue
                difference = sub(polynomial, base[p], p)
                if difference in split:
                    record = (roots_0, roots_1, split[difference])
                    if record in extension_map:
                        assert extension_map[record] == polynomial
                    extension_map[record] = polynomial
            extension_maps[p] = extension_map
            extension_sets.append(set(extension_map))
        extensions = sorted(set.intersection(*extension_sets))
        for left, right in combinations(extensions, 2):
            pair_roots = []
            for p in PRIMES:
                _locators, split = data[p]
                difference = sub(
                    extension_maps[p][left], extension_maps[p][right], p
                )
                if difference not in split:
                    break
                pair_roots.append(split[difference])
            else:
                if len(set(pair_roots)) != 1:
                    continue
                extension_pair_count += 1
                edges = {
                    (0, 1): first_roots,
                    (0, 2): triangle[0],
                    (1, 2): triangle[1],
                    (0, 3): left[0],
                    (1, 3): left[1],
                    (2, 3): left[2],
                    (0, 4): right[0],
                    (1, 4): right[1],
                    (2, 4): right[2],
                    (3, 4): pair_roots[0],
                }
                partitions = equality_partitions(5, edges)
                raw_signature = raw_compact_signature(partitions)
                if raw_signature not in canonical_cache:
                    canonical_cache[raw_signature] = canonicalize_signature(
                        raw_signature, 5
                    )
                signature = canonical_cache[raw_signature]
                signatures.setdefault(signature, (triangle, left, right))

    bounds = {
        signature: exact_dual(decode_signature(signature, 5))[0]
        for signature in signatures
    }
    maximum = max(bounds.values())
    print({
        "mode": "global_five_orbit",
        "orbit_index": orbit_index,
        "first_root_orbit_representative": first_roots,
        "primes": PRIMES,
        "normalized_nonproportional_triangles": len(triangles),
        "universal_compatible_extension_pairs": extension_pair_count,
        "raw_partition_signatures": len(canonical_cache),
        "partition_signatures": len(signatures),
        "largest_exact_dual_upper": str(maximum),
        "three_line_value": "53/6",
        "beats_three_line_value": maximum > Fraction(53, 6),
        "maximizing_example": signatures[
            next(signature for signature, value in bounds.items() if value == maximum)
        ],
    })


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--fixed-triangle", action="store_true")
    mode.add_argument("--global-triangles", action="store_true")
    mode.add_argument(
        "--global-four-orbit",
        type=int,
        choices=range(len(ORBIT_REPRESENTATIVES)),
        metavar="I",
    )
    mode.add_argument(
        "--global-five-orbit",
        type=int,
        choices=range(len(ORBIT_REPRESENTATIVES)),
        metavar="I",
    )
    args = parser.parse_args()
    data = {p: field_data(p) for p in PRIMES}
    if args.global_triangles:
        run_global_triangles(data)
    elif args.global_four_orbit is not None:
        run_global_four_orbit(data, args.global_four_orbit)
    elif args.global_five_orbit is not None:
        run_global_five_orbit(data, args.global_five_orbit)
    else:
        run_fixed(data)


if __name__ == "__main__":
    main()
