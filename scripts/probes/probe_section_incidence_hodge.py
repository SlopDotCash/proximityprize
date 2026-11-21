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
identities c = R.C and a = R.L, and the ramification budget.  Equality
occurs, so the constants in the note cannot be improved in general.

Part 2 evaluates Corollary B and Theorem C of the note at the last
second-prime predecessor (n = 2**30, rate 1/16) for irreducible factors of
value degree 3 and 4.  Value degree 2 already has a kernel-checked bound.

Part 3 evaluates Theorem D (rigidity of tangent heads) at the same cubic and
quartic, and for a multiplicity-three interpolant at the last open error count
of the first-prime rate-1/4 bracket, after checking that such an interpolant
exists by counting.

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


def incidence_bound(b, a_deg, h_gamma, h_tot):
    """Theorem A: both forms of the bound on ordinary incidences."""
    sharp = Fr(4 * b * b, (b - 1) ** 2) * (h_tot - 1) \
        * ((2 * b - 2) * h_gamma + 1) * ((2 * b - 2) * a_deg + 1)
    simple = 16 * b * b * (a_deg + 1) * (h_gamma + 1) * (h_tot - 1)
    check(sharp <= simple, 'the displayed simplification of Theorem A')
    return simple


def population_bound(n, t, d, b, h_gamma, h_tot, a_deg, weight):
    """Corollary B: sections with distinct scalars and at least t agreements
    on one irreducible factor of value degree b >= 2 and weight below t + d."""
    check(b >= 2 and t > weight - d, 'hypotheses of Corollary B')
    incidences = incidence_bound(b, a_deg, h_gamma, h_tot)
    excluded = (4 * b - 2) * h_gamma + 1    # the proof needs (4b-3)*h_gamma
    return excluded + (incidences + h_tot * n) // (t - weight + d)


def weight_free_bound(n, t, d, b, h_gamma, h_tot, a_deg):
    """Theorem C: the same population with no hypothesis on the weight."""
    check(b >= 2 and t > d, 'hypotheses of Theorem C')
    beta_x = (2 * b - 2) * h_gamma + 1
    beta_g = (2 * b - 2) * a_deg + 1
    head_case = h_tot + Fr(3 * h_gamma * (t + d), t - d)
    incidences = 4 * b * b * (b - 1) * beta_x ** 2 * beta_g
    spread_case = Fr(2 * ((h_tot + beta_x) * n + incidences), t - d)
    return (4 * b - 2) * h_gamma + 1 + int(max(head_case, spread_case))


def tangent_head_bound(n, t, d, b, h_gamma, h_tot, a_deg, weight, cbar, nbar):
    """Theorem D: the bound from rigidity of rational tangent heads.

    Returns None when the Johnson-type condition t'^2 > n d' fails.
    """
    beta_x = (2 * b - 2) * h_gamma + 1
    beta_g = (2 * b - 2) * a_deg + 1
    budget = 4 * beta_x * beta_g \
        + b * (weight * (h_tot - b) + h_tot * (weight - b * d))
    t1, d1 = t - nbar - cbar, d + 2 * cbar
    if t1 * t1 <= n * d1:
        return None
    classes = (n * (t1 - d1)) // (t1 * t1 - n * d1)
    return (4 * b - 2) * h_gamma + 1 + budget // (cbar + 1) \
        + (h_tot * n) // (nbar + 1) + h_tot * classes


def interpolant_exists(n, t, d, m, value_degree, h_tot):
    """Counting condition for a polynomial of the given value degree, total
    scalar/value degree h_tot and weight below m*t that vanishes to order m
    along every received line."""
    unknowns = sum((h_tot - l + 1) * (m * t - d * l)
                   for l in range(value_degree + 1)
                   if m * t > d * l and h_tot >= l)
    conditions = n * sum((m - l) * (h_tot - l + 1) for l in range(m))
    return unknowns > conditions


def part_three():
    """Theorem D at the terminal cubic and in the first-prime rate-1/4 bracket."""
    n = 2 ** 30
    d, t = 2 ** 26 - 1, 357913943
    terminal = []
    for b, weight, value in ((3, 290805098, 48038), (4, 302954072, 99313)):
        bound = tangent_head_bound(n, t, d, b, 34, 34, weight, weight,
                                   2 ** 24, 2 ** 23)
        check(bound == value, f'tangent-head bound, terminal b={b}')
        terminal.append((b, bound))
    d, t, m = 2 ** 28 - 1, n - 480946858, 3
    check(t == 592794966 and t * t > n * d, 'below the Johnson radius')
    check(interpolant_exists(n, t, d, m, 6, 23), 'degree 23 suffices')
    check(not interpolant_exists(n, t, d, m, 6, 22), 'degree 22 does not')
    check(m * t > 6 * d, 'value degree six fits the weight')
    expected = {2: 56175, 3: 176645, 4: 374183, 5: 648789, 6: 1000463}
    rows = []
    for b, value in expected.items():
        weight = m * t - 1
        bound = tangent_head_bound(n, t, d, b, 23, 23, weight, weight,
                                   2 ** 24, 2 ** 22)
        check(bound == value, f'tangent-head bound, multiplicity three, b={b}')
        check(1000 * bound < n, 'below a thousandth of the length')
        rows.append((b, bound))
    return terminal, rows


def part_two():
    """The last second-prime predecessor at rate 1/16.

    The weights 290805098 and 302954072 are the ones certified by the Lean
    theorems actual_cubic and actual_cubic_or_quartic; t - 1 is the weight
    bound valid for every factor of a supported interpolant.  The four
    expected values are those of the Lean theorem terminal_bounds.
    """
    n, d, t = 2 ** 30, 2 ** 26 - 1, 357913943
    check(3 * (t - 2) + 1 == n, 'n = 3r + 1 with t = r + 2')
    check(t - 290805098 + d == 134217708, 'cubic denominator')
    rows = []
    expected = {
        (3, 290805098): 360973,
        (4, 302954072): 734604,
        (3, t - 1): 887925,
        (4, t - 1): 1577981,
    }
    required = {3: 1431655733, 4: 2147483615}
    for (b, weight), value in expected.items():
        bound = population_bound(n, t, d, b, 34, 34, weight, weight)
        check(bound == value, f'population bound for b={b}, W={weight}')
        check(1000 * bound < required[b], 'three orders of magnitude of margin')
        check((2 * b - 2) * weight + 1 < 2 ** 128, 'characteristic condition')
        rows.append((b, weight, bound, required[b]))
    free = []
    for b, weight in ((3, 290805098), (4, 302954072)):
        bound = weight_free_bound(n, t, d, b, 34, 34, weight)
        check(bound < required[b], 'Theorem C also excludes the population')
        free.append((b, bound))
    return rows, free


if __name__ == '__main__':
    tight = part_one()
    print(f'del Pezzo lattice: all inequalities hold, {tight} equalities')
    rows, free = part_two()
    for b, weight, bound, need in rows:
        print(f'value degree {b}, weight <= {weight}: at most {bound} '
              f'sections; population to exclude {need}')
    for b, bound in free:
        print(f'value degree {b}, no weight hypothesis: at most {bound}')
    terminal, rows = part_three()
    for b, bound in terminal:
        print(f'tangent heads, terminal value degree {b}: at most {bound}')
    for b, bound in rows:
        print(f'tangent heads, first prime rate 1/4, value degree {b}: '
              f'at most {bound}')
    print(f'{CHECKS} explicit checks passed')
