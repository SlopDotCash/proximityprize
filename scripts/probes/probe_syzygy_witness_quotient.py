#!/usr/bin/env python3
"""Exact coding/syzygy probe for the rate-quarter predecessor.

The probe separates two superficially similar quotient proposals.

``codeword quotient``
    An event certificate is a triple ``(gamma, q, S)`` with ``q`` a decoded
    Reed--Solomon polynomial.  Identify certificates having the same ``q``.
    The hoped-for scalar-to-codeword injection is false: the exact smooth
    ``RS[32,8]/F_97`` construction has 16 distinct labels whose displayed
    decoded polynomial is identically zero.

``syzygy-pencil quotient``
    Regard a certificate as the point ``(gamma,q)`` in ``F x F^k``.  Three
    points are in the formal three-subset syzygy channel precisely when they
    lie on one affine polynomial pencil

        q_gamma = base + gamma * direction.

    Contract maximal pencils containing at least three displayed points.  If
    a pencil has a common core ``D`` and every predecessor witness has at
    least two coordinates outside ``D``, its fresh petals are disjoint and

        2 * (# labels on the pencil) <= n - T + 2.

    Consequently four guarded pencil classes contribute at most

        4 * (1 + floor((n-T)/2)).

The script performs three independent exact checks:

* full enumeration of all MCA witnesses in the known ``RS[8,2]/F_11``
  shared-fresh miniature;
* reconstruction and verification of all 48 displayed certificates in the
  smooth ``RS[32,8]/F_97`` isolated-fibre counterexample;
* integer evaluation of the same guarded capacity at the current P1
  common-factor predecessor.

No claim is made that arbitrary P1 predecessor events admit a four-pencil
cover.  That extraction is exactly the remaining geometric residual.  The
probe shows that the quotient is correctly guarded, kills the raw decoded-
codeword injection, and survives every construction tested here.

Run from the repository root:

    python3 scripts/probes/probe_syzygy_witness_quotient.py
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, product
from typing import Iterable


Polynomial = tuple[int, ...]
Point = tuple[int, Polynomial]
AffineLine = tuple[Polynomial, Polynomial]


def inv(x: int, p: int) -> int:
    assert x % p != 0
    return pow(x % p, p - 2, p)


def trim(poly: Iterable[int], p: int) -> Polynomial:
    out = [x % p for x in poly]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out or [0])


def pad(poly: Polynomial, width: int) -> Polynomial:
    assert len(poly) <= width
    return poly + (0,) * (width - len(poly))


def poly_add(a: Polynomial, b: Polynomial, p: int) -> Polynomial:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out, p)


def poly_scale(c: int, a: Polynomial, p: int) -> Polynomial:
    return trim((c * x for x in a), p)


def poly_mul(a: Polynomial, b: Polynomial, p: int) -> Polynomial:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out, p)


def poly_eval(a: Polynomial, x: int, p: int) -> int:
    out = 0
    for c in reversed(a):
        out = (out * x + c) % p
    return out


def locator(values: Iterable[int], p: int) -> Polynomial:
    out: Polynomial = (1,)
    for x in values:
        out = poly_mul(out, ((-x) % p, 1), p)
    return out


def compose_x_power(a: Polynomial, exponent: int, p: int) -> Polynomial:
    out = [0] * ((len(a) - 1) * exponent + 1)
    for i, c in enumerate(a):
        out[i * exponent] = c
    return trim(out, p)


def interpolate(points: list[tuple[int, int]], p: int) -> Polynomial:
    """Lagrange interpolation, used only for exact nonjoint certificates."""
    out: Polynomial = (0,)
    for i, (xi, yi) in enumerate(points):
        basis: Polynomial = (1,)
        denominator = 1
        for j, (xj, _yj) in enumerate(points):
            if i == j:
                continue
            basis = poly_mul(basis, ((-xj) % p, 1), p)
            denominator = denominator * (xi - xj) % p
        out = poly_add(out, poly_scale(yi * inv(denominator, p), basis, p), p)
    return out


def primitive_root(p: int) -> int:
    factors: list[int] = []
    value = p - 1
    d = 2
    while d * d <= value:
        if value % d == 0:
            factors.append(d)
            while value % d == 0:
                value //= d
        d += 1
    if value > 1:
        factors.append(value)
    for g in range(2, p):
        if all(pow(g, (p - 1) // ell, p) != 1 for ell in factors):
            return g
    raise AssertionError("prime field has no primitive root")


def line_through(a: Point, b: Point, p: int) -> AffineLine:
    ga, qa = a
    gb, qb = b
    assert ga != gb and len(qa) == len(qb)
    scalar = inv(gb - ga, p)
    slope = tuple((y - x) * scalar % p for x, y in zip(qa, qb))
    base = tuple((x - ga * d) % p for x, d in zip(qa, slope))
    return base, slope


def point_on_line(point: Point, line: AffineLine, p: int) -> bool:
    gamma, q = point
    base, slope = line
    return all(x == (b + gamma * d) % p for x, b, d in zip(q, base, slope))


def rich_lines(points: list[Point], p: int, minimum: int = 3) -> list[tuple[AffineLine, tuple[int, ...]]]:
    candidates = {
        line_through(a, b, p)
        for a, b in combinations(points, 2)
        if a[0] != b[0]
    }
    out = []
    for line in candidates:
        members = tuple(i for i, point in enumerate(points) if point_on_line(point, line, p))
        if len(members) >= minimum:
            out.append((line, members))
    return sorted(out, key=lambda item: (-len(item[1]), item[0]))


def syzygy_component_count(points: list[Point], lines: list[tuple[AffineLine, tuple[int, ...]]]) -> int:
    """Connected components after contracting every rich affine pencil."""
    parent = list(range(len(points)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def union(i: int, j: int) -> None:
        ri, rj = find(i), find(j)
        if ri != rj:
            parent[rj] = ri

    for _line, members in lines:
        for i in members[1:]:
            union(members[0], i)
    return len({find(i) for i in range(len(points))})


def maximum_codeword_matching(graph: dict[int, set[Polynomial]]) -> int:
    """Maximum matching from scalar labels to displayed decoded polynomials."""
    owner: dict[Polynomial, int] = {}

    def augment(gamma: int, seen: set[Polynomial]) -> bool:
        for q in sorted(graph[gamma]):
            if q in seen:
                continue
            seen.add(q)
            if q not in owner or augment(owner[q], seen):
                owner[q] = gamma
                return True
        return False

    return sum(augment(gamma, set()) for gamma in sorted(graph))


def guarded_pencil_capacity(n: int, threshold: int) -> int:
    """Capacity of one common-core pencil under ``|D|+2 <= threshold``."""
    assert threshold <= n
    return 1 + (n - threshold) // 2


def check_f11_full_enumeration() -> dict[str, int]:
    """Fully enumerate the known shared-fresh RS[8,2]/F_11 stack."""
    p, n, k, threshold = 11, 8, 2, 4
    domain = list(range(n))
    q0, q1 = (1, 2), (3, 1)
    joint = (0, 1, 2, 3)
    gammas = (1, 2, 3)
    witnesses = ((0, 4, 5, 6), (1, 4, 5, 7), (2, 4, 6, 7))

    u0: list[int | None] = [None] * n
    u1: list[int | None] = [None] * n
    for e in joint:
        u0[e] = poly_eval(q0, domain[e], p)
        u1[e] = poly_eval(q1, domain[e], p)
    u0[4], u1[4] = 1, 1

    decoded = []
    for j, gamma in enumerate(gammas):
        anchor = j
        x0, x1 = domain[anchor], domain[4]
        y0 = (int(u0[anchor]) + gamma * int(u1[anchor])) % p
        y1 = (int(u0[4]) + gamma * int(u1[4])) % p
        slope = (y1 - y0) * inv(x1 - x0, p) % p
        decoded.append(((y0 - slope * x0) % p, slope))

    for e, (i, j) in {5: (0, 1), 6: (0, 2), 7: (1, 2)}.items():
        gi, gj = gammas[i], gammas[j]
        yi = poly_eval(decoded[i], domain[e], p)
        yj = poly_eval(decoded[j], domain[e], p)
        u1[e] = (yj - yi) * inv(gj - gi, p) % p
        u0[e] = (yi - gi * int(u1[e])) % p

    row0 = [int(x) for x in u0]
    row1 = [int(x) for x in u1]
    assert 0 not in row1

    def degree_one_explainable(row: list[int], support: tuple[int, ...]) -> bool:
        if len(support) <= k:
            return True
        a, b = support[:2]
        slope = (row[b] - row[a]) * inv(domain[b] - domain[a], p) % p
        base = (row[a] - slope * domain[a]) % p
        return all((base + slope * domain[e]) % p == row[e] for e in support)

    graph: dict[int, set[Polynomial]] = {}
    selected_support: dict[tuple[int, Polynomial], tuple[int, ...]] = {}
    for gamma in range(p):
        candidates: set[Polynomial] = set()
        for q in product(range(p), repeat=k):
            agreement = tuple(
                e for e, x in enumerate(domain)
                if poly_eval(q, x, p) == (row0[e] + gamma * row1[e]) % p
            )
            for size in range(threshold, len(agreement) + 1):
                for support in combinations(agreement, size):
                    joint_here = (
                        degree_one_explainable(row0, support)
                        and degree_one_explainable(row1, support)
                    )
                    if not joint_here:
                        candidates.add(q)
                        selected_support[(gamma, q)] = support
                        break
                if q in candidates:
                    break
        if candidates:
            graph[gamma] = candidates

    expected = {
        0: {(1, 2)},
        1: {(4, 5)},
        2: {(10, 1)},
        3: {(3, 3)},
        4: {(9, 0)},
        6: {(8, 8)},
        7: {(0, 9)},
    }
    assert graph == expected
    points = [(gamma, next(iter(qs))) for gamma, qs in sorted(graph.items())]
    lines = rich_lines(points, p)
    assert [len(members) for _line, members in lines] == [3]
    assert syzygy_component_count(points, lines) == 5
    assert maximum_codeword_matching(graph) == len(graph) == 7
    assert all(selected_support[key] for key in selected_support)
    return {
        "bad_scalars": len(graph),
        "distinct_codewords": len({q for qs in graph.values() for q in qs}),
        "matching": maximum_codeword_matching(graph),
        "rich_lines": len(lines),
        "largest_line": len(lines[0][1]),
        "syzygy_classes": syzygy_component_count(points, lines),
    }


def check_f97_displayed_construction() -> dict[str, int]:
    """Reconstruct every displayed witness in the smooth F_97 counterexample."""
    p, n, k = 97, 32, 8
    bad_threshold, predecessor_threshold = 17, 18
    omega = pow(primitive_root(p), (p - 1) // n, p)
    domain = [pow(omega, e, p) for e in range(n)]
    assert len(set(domain)) == n and pow(omega, n // 2, p) == p - 1
    zeta = pow(omega, 2, p)

    exponent_sets = ({0, 1, 8}, {2, 9, 10}, {3, 5, 7})
    locators = [locator((pow(zeta, e, p) for e in sorted(es)), p) for es in exponent_sets]
    pa, pb, pc = locators
    lam = next(
        (pc[j] - pa[j]) * inv(pb[j] - pa[j], p) % p
        for j in range(3) if pa[j] != pb[j]
    )
    assert pc == poly_add(poly_scale(1 - lam, pa, p), poly_scale(lam, pb, p), p)
    factors = (
        (0,),
        compose_x_power(poly_scale(1 - lam, pa, p), 2, p),
        compose_x_power(pc, 2, p),
    )

    def fibre(exponents: set[int]) -> set[int]:
        return {e for e in range(n) if e % 16 in exponents}

    pair12, pair23, pair13 = (fibre(es) for es in exponent_sets)
    private = [fibre(es) for es in ({4, 6}, {11, 12}, {13, 14})]
    cores = (
        pair12 | pair13 | private[0],
        pair12 | pair23 | private[1],
        pair13 | pair23 | private[2],
    )
    hole = fibre({15})
    assert all(len(core) == 16 for core in cores)
    assert len(set().union(*cores)) == 30 and len(hole) == 2

    alpha = beta = None
    for aa, bb in product(range(1, p), repeat=2):
        constants = []
        valid = True
        for f in factors:
            value = poly_eval(f, domain[next(iter(hole))], p)
            if bb == value:
                valid = False
                break
            constants.append((value - aa) * inv(bb - value, p) % p)
        if not valid:
            continue
        unsafe = [{c * domain[e] % p for e in hole} for c in constants]
        safe = {(-domain[e]) % p for e in set().union(*cores)}
        if any(safe & labels for labels in unsafe):
            continue
        if any(unsafe[i] & unsafe[j] for i in range(3) for j in range(i)):
            continue
        alpha, beta = aa, bb
        break
    assert alpha is not None and beta is not None

    u0, u1 = [0] * n, [0] * n
    for e, x in enumerate(domain):
        owners = [i for i, core in enumerate(cores) if e in core]
        if not owners:
            assert e in hole
            u0[e], u1[e] = alpha * x % p, beta
        else:
            values = {poly_eval(factors[i], x, p) for i in owners}
            assert len(values) == 1
            value = values.pop()
            u0[e], u1[e] = value * x % p, value

    source_lines: list[AffineLine] = []
    for f, core in zip(factors, cores):
        intercept = poly_mul(f, (0, 1), p)
        direction = f
        assert len(intercept) - 1 < k and len(direction) - 1 < k
        anchors = sorted(core)[:k]
        forced0 = interpolate([(domain[e], u0[e]) for e in anchors], p)
        forced1 = interpolate([(domain[e], u1[e]) for e in anchors], p)
        assert forced0 == intercept and forced1 == direction
        source_lines.append((pad(intercept, k), pad(direction, k)))

    points: list[Point] = []
    graph: dict[int, set[Polynomial]] = defaultdict(set)
    supports: dict[Point, set[int]] = {}
    source_of: dict[Point, int] = {}
    for i, (f, core) in enumerate(zip(factors, cores)):
        intercept = poly_mul(f, (0, 1), p)
        direction = f
        for e, x in enumerate(domain):
            if e in core:
                continue
            denominator = (u1[e] - poly_eval(direction, x, p)) % p
            numerator = (poly_eval(intercept, x, p) - u0[e]) % p
            assert denominator != 0
            gamma = numerator * inv(denominator, p) % p
            q = poly_add(intercept, poly_scale(gamma, direction, p), p)
            point = (gamma, pad(q, k))
            support = set(core) | {e}
            assert len(support) == bad_threshold
            assert all(
                poly_eval(q, domain[j], p) == (u0[j] + gamma * u1[j]) % p
                for j in support
            )
            # The first k core values force the joint explaining pair to be
            # this source line; it genuinely misses at the fresh coordinate.
            assert (poly_eval(intercept, x, p), poly_eval(direction, x, p)) != (u0[e], u1[e])
            assert point not in supports
            points.append(point)
            graph[gamma].add(point[1])
            supports[point] = support
            source_of[point] = i

    assert len(points) == 48 and len(set(points)) == 48
    assert len(graph) == 36
    all_codewords = {q for qs in graph.values() for q in qs}
    assert len(all_codewords) == 33
    zero = (0,) * k
    zero_labels = {gamma for gamma, qs in graph.items() if zero in qs}
    assert len(zero_labels) == 16
    zero_only_labels = {gamma for gamma, qs in graph.items() if qs == {zero}}
    # This is an explicit Hall obstruction: eight scalar vertices have the
    # singleton neighbour set {0}, so at least seven must remain unmatched.
    assert len(zero_only_labels) == 8
    matching = maximum_codeword_matching(graph)
    assert matching == 29 < len(graph)

    # Every repeated decoded codeword forces witness intersections into the
    # zero set of u1.  The zero polynomial is the only repeated codeword here.
    zero_positions = {e for e, value in enumerate(u1) if value == 0}
    assert len(zero_positions) == 16
    zero_points = [point for point in points if point[1] == zero]
    for a, b in combinations(zero_points, 2):
        assert supports[a] & supports[b] <= zero_positions

    lines = rich_lines(points, p)
    assert [len(members) for _line, members in lines] == [16, 16, 16]
    assert {line for line, _members in lines} == set(source_lines)
    assert syzygy_component_count(points, lines) == 3
    assert all(len({source_of[points[j]] for j in members}) == 1 for _line, members in lines)

    bad_one_fresh = (n - len(cores[0])) // (bad_threshold - len(cores[0]))
    predecessor_two_fresh = (n - len(cores[0])) // (predecessor_threshold - len(cores[0]))
    assert bad_one_fresh == 16
    assert predecessor_two_fresh == guarded_pencil_capacity(n, predecessor_threshold) == 8
    assert 3 * predecessor_two_fresh == 24 < n
    assert 4 * predecessor_two_fresh == n
    assert not (len(zero_positions) < 2 * bad_threshold - n)
    assert not (len(zero_positions) < 2 * predecessor_threshold - n)

    return {
        "displayed_points": len(points),
        "bad_scalar_labels": len(graph),
        "distinct_decoded_codewords": len(all_codewords),
        "maximum_displayed_matching": matching,
        "zero_codeword_labels": len(zero_labels),
        "zero_only_hall_labels": len(zero_only_labels),
        "direction_zero_positions": len(zero_positions),
        "rich_lines": len(lines),
        "line_sizes": len(lines[0][1]),
        "syzygy_classes": syzygy_component_count(points, lines),
        "bad_one_fresh_capacity_per_line": bad_one_fresh,
        "predecessor_two_fresh_capacity_per_line": predecessor_two_fresh,
        "three_line_predecessor_cap": 3 * predecessor_two_fresh,
        "four_line_predecessor_cap": 4 * predecessor_two_fresh,
    }


def check_p1_predecessor_arithmetic() -> dict[str, int]:
    """Current common-factor construction and its immediate predecessor."""
    m = 2**26
    n = 2**30
    k = 2**28
    saturated_core = (53 * m - 8) // 6
    bad_threshold = saturated_core + 1
    predecessor_threshold = saturated_core + 2
    assert saturated_core == 592_794_964
    assert bad_threshold == 592_794_965
    assert predecessor_threshold == 592_794_966
    assert k == 4 * m and n == 16 * m

    # The construction is covered by three source pencils.  Source zero has
    # intercept=direction=0, so all of its one-fresh labels use exactly the
    # same decoded polynomial.  This is a symbolic, not enumerative, repeat.
    repeated_zero_codeword_labels = n - saturated_core
    assert repeated_zero_codeword_labels == 480_946_860

    per_line = guarded_pencil_capacity(n, predecessor_threshold)
    assert per_line == 240_473_430
    three_line_cap = 3 * per_line
    four_line_cap = 4 * per_line
    assert three_line_cap == 721_420_290 < n
    assert four_line_cap == 961_893_720 < n
    assert n - four_line_cap == 111_848_104
    assert 2 * predecessor_threshold - n == 111_848_108

    return {
        "n": n,
        "k": k,
        "bad_threshold": bad_threshold,
        "predecessor_threshold": predecessor_threshold,
        "known_bad_scalars": n + 2,
        "repeated_zero_codeword_labels": repeated_zero_codeword_labels,
        "guarded_capacity_per_pencil": per_line,
        "three_pencil_cap": three_line_cap,
        "four_pencil_cap": four_line_cap,
        "four_pencil_slack": n - four_line_cap,
    }


def print_block(title: str, values: dict[str, int]) -> None:
    print(title)
    for key, value in values.items():
        print(f"  {key}={value}")


def main() -> None:
    f11 = check_f11_full_enumeration()
    f97 = check_f97_displayed_construction()
    p1 = check_p1_predecessor_arithmetic()

    print("SYZYGY WITNESS-QUOTIENT PROBE: PASS")
    print_block("F11_FULL_ENUMERATION", f11)
    print_block("F97_DISPLAYED_COUNTEREXAMPLE", f97)
    print_block("P1_COMMON_FACTOR_PREDECESSOR", p1)
    print("VERDICT_CODEWORD_QUOTIENT=REFUTED")
    print("  F97 displayed scalar-to-codeword matching is 29 < 36;")
    print("  at P1 one decoded zero polynomial carries 480946860 labels.")
    print("VERDICT_ZERO_OVERLAP_GUARD=TOO_NARROW")
    print("  F97 has |zero(u1)|=16 while 2T-n is only 2 (bad) or 4 (predecessor).")
    print("VERDICT_FOUR_PENCIL_TWO_FRESH_GUARD=SURVIVES")
    print("  exact P1 guarded cap is 961893720 < 1073741824 (slack 111848104).")
    print("OPEN_EXTRACTION=prove every over-budget P1 predecessor family is covered")
    print("  by at most four affine decoded-codeword pencils with the two-fresh guard.")


if __name__ == "__main__":
    main()
