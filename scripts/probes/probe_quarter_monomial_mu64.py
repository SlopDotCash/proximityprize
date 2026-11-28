#!/usr/bin/env python3
"""Check arbitrary target triples for degree <=15 monomial cross ratios over p1.

Run with uv run --with python-flint python scripts/probes/probe_quarter_monomial_mu64.py.
"""
from collections import Counter, defaultdict
from itertools import combinations, product
from math import gcd

from flint import fmpz_mod_poly_ctx
from probe_rate_half_eight_fibers import G, N, P

GRID = 64
ROOTS = [pow(G, j * (N // GRID), P) for j in range(GRID)]
ROOT_SET = set(ROOTS)
POLY = fmpz_mod_poly_ctx(P)
X = POLY([0, 1])
ONE = POLY([1])
PAIRINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def normalize(values):
    unit = pow(next(v for v in values if v % P), -1, P)
    return tuple(unit*v % P for v in values)


def spectrum(exponents):
    groups = [[exponents[i]+exponents[j] for i, j in matching] for matching in PAIRINGS]
    return min(tuple(sorted(tuple(sorted(w*(x-shift) % GRID for x in pair)) for pair in groups))
               for w in range(1, GRID, 2) for shift in set(sum(groups, [])))


def add_row(row, basis):
    row = list(row)
    for pivot, previous in basis:
        multiplier = row[pivot]
        if multiplier:
            for j in range(pivot+1, len(row)):
                row[j] = (row[j]-multiplier*previous[j]) % P
            row[pivot] = 0
    for j, value in enumerate(row):
        if value:
            return tuple(sorted(basis+((j, normalize(row)),)))
    return basis


def nullspace(basis, width):
    pivots = {j for j, _ in basis}
    columns = []
    for free in (j for j in range(width) if j not in pivots):
        vector = [0]*width
        vector[free] = 1
        for pivot, row in reversed(basis):
            vector[pivot] = -sum(row[j]*vector[j] for j in range(pivot+1, width)) % P
        columns.append(vector)
    return columns


def spectrum_requires_grid_triple(groups):
    """All permissible 12-root polynomials found must have 16 or more roots."""
    frequencies = sorted(set(sum(groups, ())))
    assert len(frequencies) in (5, 6)
    indices = [(frequencies.index(i), frequencies.index(j)) for i, j in groups]
    required = {k for i, j in indices if i != j for k in (i, j)}
    rows = [[ROOTS[h*f % GRID] for f in frequencies] for h in range(GRID)]
    visited = set()
    needs_triple = False

    def allowed(vector):
        if not all(vector[k] % P for k in required):
            return False
        if len(frequencies) == 5:
            return True
        a, b, c = [vector[i]*vector[j] % P for i, j in indices]
        return ((a+b-c)**2-4*a*b) % P == 0

    def record(vector, roots):
        nonlocal needs_triple
        if allowed(vector):
            assert roots >= 16, (groups, vector, roots)
            needs_triple = True

    def explore(basis):
        nonlocal needs_triple
        columns = nullspace(basis, len(frequencies))
        if not columns or not all(any(v[k] for v in columns) for k in required):
            return
        evaluations = list(zip(*[[sum(x*y for x, y in zip(v, row)) % P for row in rows]
                                 for v in columns]))
        common = tuple(i for i, v in enumerate(evaluations) if not any(v))
        if common in visited:
            return
        visited.add(common)
        if len(common) >= 12:
            if len(columns) == 1:
                record(columns[0], len(common))
            else:
                assert len(common) >= 16, (groups, common)
                needs_triple = True
            return
        if len(columns) == 2:
            classes = Counter()
            for a, b in evaluations:
                if a or b:
                    classes[a*pow(b, -1, P) % P if b else None] += 1
            left, right = columns
            for value, count in classes.items():
                if count+len(common) >= 12:
                    vector = right if value is None else [x-value*y for x, y in zip(left, right)]
                    record(vector, count+len(common))
        elif len(columns) > 2:
            for i, row in enumerate(rows):
                if i not in common:
                    explore(add_row(row, basis))

    for other in combinations(range(1, 17), 3):
        basis = ()
        for i in (0, *other):
            basis = add_row(rows[i], basis)
        explore(basis)
    return needs_triple


def degree_function(a, free):
    fixed = [i for i in range(4) if i != free]
    base_gcd = gcd(*[a[j]-a[fixed[0]] for j in fixed])
    raw = a[3]+a[2]-a[1]
    conditions = []
    for i, j in combinations(fixed, 2):
        g = gcd(a[j]-a[i], a[free]-a[i])
        conditions.append((g, (a[j]-a[i])//g))

    def degree(is_unity):
        return raw-base_gcd-sum(g for g, k in conditions if is_unity(k))+2*int(is_unity(base_gcd))

    return degree, {k for _, k in conditions} | {base_gcd}


def site_map(a, free, h, parameter):
    """Return homogeneous affine forms in the one unknown, or a specialized constant."""
    values = [ROOTS[h*j % GRID] for j in a]
    if parameter is not None:
        values[free] = values[free]*parameter % P
    products = []
    for matching in PAIRINGS[:2]:
        order, const, linear = 0, 1, 0
        for i, j in matching:
            if parameter is None and free in (i, j):
                delta, slope = (-values[j], values[i]) if free == i else (values[i], -values[j])
                const, linear = const*delta % P, const*slope % P
            else:
                delta = values[i]-values[j]
                if not delta:
                    delta = (a[i]-a[j])*values[i]
                    order += 1
                const, linear = const*delta % P, linear*delta % P
        products.append((order, const, linear))
    (vp, pa, pb), (vq, qa, qb) = products
    if vp != vq:
        return (0, 0, 1, 0) if vp > vq else (1, 0, 0, 0)
    if (pa*qb-pb*qa) % P == 0:
        return normalize((pa, 0, qa, 0) if pa or qa else (pb, 0, qb, 0))
    return normalize((pa, pb, qa, qb))


def top_three(groups):
    return sum(sorted(groups.values(), reverse=True)[:3])


def check_one_parameter(a, free):
    degree, orders = degree_function(a, free)
    for j, param in enumerate(ROOTS):
        m = degree(lambda k: j*k % GRID == 0)
        if 13 <= m <= 15:
            fibers = Counter(site_map(a, free, i, param) for i in range(GRID))
            assert 2*top_three(fibers)-3*m <= 36

    generic = Counter(site_map(a, free, i, None) for i in range(GRID))
    generic_count = top_three(generic)
    generic_degree = degree(lambda _: False)
    if 13 <= generic_degree <= 15:
        assert 2*generic_count-3*generic_degree <= 36
    # Collect event roots with enough pair coincidences to reach 38 actual sites.
    weights = Counter()
    for (lhs, left_count), (rhs, right_count) in combinations(generic.items(), 2):
        p, q, c, d = lhs
        f, g, h, i = rhs
        terms = [(p*h-f*c) % P, (p*i+q*h-f*d-g*c) % P, (q*i-g*d) % P]
        while terms and not terms[-1]:
            terms.pop()
        if len(terms) > 1:
            weights[normalize(terms)] += left_count*right_count
    events = ONE
    for coefficients, weight in weights.items():
        events *= POLY(list(coefficients))**weight
    factors = []
    for group, multiple in events.factor_squarefree()[1]:
        if multiple >= max(1, 38-generic_count):
            factors.extend(f for f, _ in group.factor()[1])
    for k in orders:
        factors.extend(f for f, _ in (X**k-1).factor()[1])
    for f in factors:
        if f.degree() == 1 and (-int(f[0])) % P in ROOT_SET | {0}:
            continue
        m = degree(lambda k: X.pow_mod(k, f) == ONE)
        if not 13 <= m <= 15:
            continue
        fibers = Counter()
        for (pa, pb, qa, qb), count in generic.items():
            up, down = POLY([pa, pb]) % f, POLY([qa, qb]) % f
            key = tuple(map(int, (up*down.inverse_mod(f) % f).coeffs())) if down else None
            fibers[key] += count
        assert 2*top_three(fibers)-3*m <= 36


def repeated_exponents():
    checked = 0
    for j, k in combinations([u for u in range(-17, 18) if u], 2):
        if gcd(j, k) != 1:
            continue
        exps = (0, 0, j, k)
        a, b, c, d = sorted(exps)
        raw = c+d-a-b
        if not 13 <= raw <= 17:
            continue
        seen = set()
        for e, f in product(range(GRID), repeat=2):
            if (e, f) in seen:
                continue
            seen.update(((e+h*j) % GRID, (f+h*k) % GRID) for h in range(GRID))
            m = raw-sum((k*e-j*f-(k-j)*offset) % GRID == 0 for offset in (0, 32))
            if not 13 <= m <= 15:
                continue
            checked += 1
            fibers = Counter()
            for h in range(GRID):
                values = (1, P-1, ROOTS[(h*j+e) % GRID], ROOTS[(h*k+f) % GRID])
                products = []
                for matching in PAIRINGS[:2]:
                    order, coeff = 0, 1
                    for i, l in matching:
                        delta = values[i]-values[l]
                        if not delta:
                            delta = (exps[i]-exps[l])*values[i]
                            order += 1
                        coeff = coeff*delta % P
                    products.append((order, coeff))
                (vp, up), (vq, down) = products
                target = None if vp < vq else 0 if vp > vq else up*pow(down, -1, P) % P
                fibers[target] += 1
            assert 2*top_three(fibers)-3*m <= 36
    return checked


def main():
    spectra = defaultdict(list)
    for tail in combinations(range(1, 43), 3):
        if gcd(*tail) != 1:
            continue
        a = (0, *tail)
        loss = sum(gcd(k-i, j-i) for i, j, k in combinations(a, 3))
        if a[3]+a[2]-a[1]-loss <= 15:
            spectra[spectrum(a)].append(a)
    candidates = [a for group, tuples in spectra.items() if spectrum_requires_grid_triple(group)
                  for a in tuples]
    for a in candidates:
        for free in range(4):
            check_one_parameter(a, free)
    repeated = repeated_exponents()
    assert (len(spectra),sum(map(len, spectra.values())),len(candidates),repeated) == (204,575,19,3284)
    print("spectra", len(spectra), "tuples", sum(map(len, spectra.values())),
          "with grid triple to check", len(candidates), "repeated-exponent phases", repeated)


if __name__ == "__main__":
    main()
