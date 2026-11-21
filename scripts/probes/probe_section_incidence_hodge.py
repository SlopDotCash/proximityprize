#!/usr/bin/env python3
"""Exact checks for the Hodge-index section-incidence bound.

Part 1 verifies the lattice inequalities of
docs/research/proximity-gap/section-incidence-hodge-index.md on the quartic
del Pezzo surface, where every intersection number is explicit.  The conic
bundles |H-E1| and |2H-E2-E3-E4-E5| make it a double cover of P1 x P1.
Components of singular fibres of the second bundle are sections of the
first; components of singular fibres of the first are the "lines".  The
script checks, for every section and every choice of one line per site,

    c * sum(a_x)  >=  (m * (1 - 1/b))**2 ,

the pair inequality for sections in different fibres, the adjunction
identities c = R.C and a = R.L, and the ramification budget.  The local
Bessel inequality attains equality for eight combinations.

Part 2 evaluates the population bound at the last second-prime predecessor
(n = 2**30, rate 1/16) for factors of value degree 3 and 4.

All arithmetic is exact.  Checks are explicit calls, so they also run under
`python3 -O`.
"""
from fractions import Fraction as Fr
from itertools import combinations

CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise SystemExit(f'CHECK FAILED: {message}')


def cls(h, *minus):
    """The class h*H - sum_{i in minus} E_i, stored as (h, m_1, ..., m_5)."""
    v = [h, 0, 0, 0, 0, 0]
    for i in minus:
        v[i] += 1
    return tuple(v)


def exceptional(i):
    """The class E_i = 0*H - (-1)*E_i."""
    v = [0] * 6
    v[i] = -1
    return tuple(v)


def dot(u, v):
    """Intersection form of signature (1,5): H^2 = 1, E_i^2 = -1."""
    return u[0] * v[0] - sum(a * b for a, b in zip(u[1:], v[1:]))


def add(u, v, s=1):
    return tuple(a + s * b for a, b in zip(u, v))


def part_one():
    b = 2
    phi_x = cls(1, 1)                       # pencil of lines through p1
    phi_g = cls(2, 2, 3, 4, 5)              # pencil of conics through p2..p5
    canonical = tuple(-c for c in cls(3, 1, 2, 3, 4, 5))   # K = -3H + sum E_i
    check(dot(canonical, canonical) == 4, 'K^2 = 4 on the quartic del Pezzo')
    check(dot(phi_x, phi_x) == 0 and dot(phi_g, phi_g) == 0, 'fibre squares')
    check(dot(phi_x, phi_g) == b, 'covering degree')
    ram = add(canonical, add(phi_x, phi_g))
    ram = add(ram, add(phi_x, phi_g))       # R = K + 2 phi_x + 2 phi_g

    lines = {j: {'+': exceptional(j), '-': cls(1, 1, j)} for j in range(2, 6)}
    conic = cls(2, 1, 2, 3, 4, 5)
    fibres = []
    for i, j in ((2, 3), (2, 4), (2, 5)):
        k, l = sorted(set(range(2, 6)) - {i, j})
        fibres.append((cls(1, i, j), cls(1, k, l)))
    fibres.append((conic, exceptional(1)))
    sections = [c for pair in fibres for c in pair]

    for first, second in fibres:
        check(add(first, second) == phi_g, 'fibre of the conic pencil')
        check(dot(first, second) == 1, 'fibre components meet once')
    for section in sections:
        check(dot(section, phi_x) == 1, 'section of the first pencil')
        check(dot(section, phi_g) == 0, 'section lies in a fibre')
        check(-dot(section, section) == dot(ram, section) == 1, 'c = R.C')
    for j, pair in lines.items():
        check(add(pair['+'], pair['-']) == phi_x, 'reducible line fibre')
        for line in pair.values():
            check(dot(line, phi_g) == 1 and dot(line, phi_x) == 0, 'line')
            check(-dot(line, line) == dot(ram, line) == 1, 'a = R.L')

    equalities = 0
    for section in sections:
        c = -dot(section, section)
        for signs in range(16):
            chosen = [lines[j]['+' if (signs >> (j - 2)) & 1 else '-']
                      for j in range(2, 6)]
            for line in chosen:
                check(dot(section, line) in (0, 1), 'incidence is 0 or 1')
            met = [line for line in chosen if dot(section, line) == 1]
            if met:
                lhs = c * sum(-dot(line, line) for line in met)
                rhs = (Fr(len(met)) * (1 - Fr(1, b))) ** 2
                check(lhs >= rhs, 'Bessel inequality')
                equalities += lhs == rhs
    check(equalities > 0, 'the Bessel inequality is attained')

    plus = [lines[j]['+'] for j in range(2, 6)]
    for f1, f2 in combinations(range(4), 2):
        for c1 in fibres[f1]:
            for c2 in fibres[f2]:
                check(dot(c1, c2) == 0, 'sections in different fibres')
                only1 = sum(dot(c1, l) == 1 and dot(c2, l) == 0 for l in plus)
                only2 = sum(dot(c2, l) == 1 and dot(c1, l) == 0 for l in plus)
                check(2 * min(only1, only2) <= 1 * (1 + 1), 'pair inequality')

    beta_x, beta_g = dot(ram, phi_x), dot(ram, phi_g)
    check((beta_x, beta_g) == (2, 2), 'branch bidegree')
    check(sum(dot(ram, s) for s in sections) <= 2 * 4 * beta_x * beta_g,
          'ramification budget with two sections per fibre')
    return equalities


def population_bound(n, t, d, b, h_gamma, h_tot, a_deg, weight):
    """Sections with distinct scalars and at least t agreements on one
    irreducible factor of value degree b >= 2 (Corollary B of the note)."""
    check(b >= 2 and t > weight - d, 'hypotheses of the population bound')
    incidences = 16 * b**2 * (a_deg + 1) * (h_gamma + 1) * (h_tot - 1)
    excluded = (4 * b - 2) * h_gamma + 1
    return excluded + (incidences + h_tot * n) // (t - weight + d)


def part_two():
    n, d, t = 2 ** 30, 2 ** 26 - 1, 357913943
    check(3 * (t - 2) + 1 == n, 'n = 3r + 1 with t = r + 2')
    rows = []
    for b, need, weight, expected, expected_weighted in (
        (3, 1431655733, 290805098, 887925, 360973),
        (4, 2147483615, 302954072, 1577981, 734604),
    ):
        bound = population_bound(n, t, d, b, 34, 34, t - 1, t - 1)
        weighted_bound = population_bound(n, t, d, b, 34, 34, weight, weight)
        check((bound, weighted_bound) == (expected, expected_weighted), 'Corollary B terminal values')
        check(1000 * bound < need, 'three orders of magnitude of margin')
        rows.append((b, bound, weighted_bound, need))
    return rows


if __name__ == '__main__':
    tight = part_one()
    print(f'del Pezzo lattice: all inequalities hold, {tight} equalities')
    for b, bound, weighted_bound, need in part_two():
        print(f'value degree {b}: at most {bound} sections, '
              f'or {weighted_bound} using the actual weight, terminal population {need}')
    print(f'{CHECKS} explicit checks passed')
