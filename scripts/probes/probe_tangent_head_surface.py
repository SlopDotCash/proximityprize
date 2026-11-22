#!/usr/bin/env python3
"""Tangent heads on explicit interpolation surfaces over a prime field.

Theorem D' of docs/research/proximity-gap/section-incidence-hodge-index.md
has a geometric half that is not formalized.  This script tests its concrete
consequences on surfaces built by exact linear algebra over F_p.

For chosen polynomial sections (z_i, q_i) and received lines, it solves for a
polynomial F(X, Z, Y) of prescribed support that contains every section,
contains chosen received lines simply, and vanishes to order two along
others.  For every section it forms

    V = -F_Z(X, z, q) / F_Y(X, z, q),        R = q - z V,

reduces V to lowest terms and checks:

  1. at every agreement site where the reduced denominator is nonzero,
     V equals the second received row and R the first, including sites
     where F is singular along the received line;
  2. the number of agreement sites at core lines where this fails is at most
     the height of V;
  3. the heights of sections with distinct scalars sum to at most
     C' = 2 B_X B_Z + b (W (m - b) + m (W - b d));
  4. for value degree two, the discriminant at the scalar of a section is the
     square of F_Y on the section;
  5. the bound of Theorem D' holds for the family;
  6. on these instances every height equals W - d minus the number of
     double lines through the section.

All arithmetic is exact in F_p.  Checks are explicit calls, so the script
also runs under `python3 -O`.
"""
import random

P = 10007
CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise SystemExit(f'CHECK FAILED: {message}')


# ---- univariate polynomials over F_p as coefficient lists, low degree first

def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % P
                 for i in range(n)])


def pscale(a, c):
    return trim([(x * c) % P for x in a])


def psub(a, b):
    return padd(a, pscale(b, P - 1))


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def pdivmod(a, b):
    a = a[:]
    q = [0] * max(0, len(a) - len(b) + 1)
    inv = pow(b[-1], P - 2, P)
    while len(a) >= len(b):
        c = (a[-1] * inv) % P
        shift = len(a) - len(b)
        q[shift] = c
        for i, y in enumerate(b):
            a[shift + i] = (a[shift + i] - c * y) % P
        trim(a)
    return trim(q), a


def pgcd(a, b):
    a, b = a[:], b[:]
    while b:
        a, b = b, pdivmod(a, b)[1]
    return a


def peval(a, x):
    value = 0
    for c in reversed(a):
        value = (value * x + c) % P
    return value


def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out


def deg(a):
    return len(a) - 1


def rand_poly(rng, degree):
    return trim([rng.randrange(P) for _ in range(degree + 1)]) or [1]


# ---- linear algebra over F_p

def nullspace(rows, ncols):
    rows = [r[:] for r in rows]
    pivots = []
    rank = 0
    for col in range(ncols):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], P - 2, P)
        rows[rank] = [(x * inv) % P for x in rows[rank]]
        lead = rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                c = rows[i][col]
                rows[i] = [(x - c * y) % P for x, y in zip(rows[i], lead)]
        pivots.append(col)
        rank += 1
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        vec = [0] * ncols
        vec[f] = 1
        for i, col in enumerate(pivots):
            vec[col] = (-rows[i][f]) % P
        basis.append(vec)
    return basis


# ---- surfaces

class Surface:
    """F = sum of coeff[(j, c)] (a polynomial in X) times Y^j Z^c."""

    def __init__(self, b, m, d, weight, coeff):
        self.b, self.m, self.d, self.weight, self.coeff = b, m, d, weight, coeff

    def on_section(self, z, q, dy=0, dz=0):
        """The Hasse derivative of order (dy, dz) in (Y, Z) at (X, z, q(X))."""
        total = []
        powers = [ppow(q, k) for k in range(self.b + 1)]
        for (j, c), poly in self.coeff.items():
            if j < dy or c < dz:
                continue
            factor = 1
            for k in range(dy):
                factor = factor * (j - k) % P
            for k in range(dz):
                factor = factor * (c - k) % P
            factor = factor * pow(z, c - dz, P) % P
            total = padd(total, pscale(pmul(poly, powers[j - dy]), factor))
        return total

    def y_coefficient(self, z, j):
        total = []
        for (jj, c), poly in self.coeff.items():
            if jj == j:
                total = padd(total, pscale(poly, pow(z, c, P)))
        return total


def monomials(b, m, d, weight):
    return [(j, c, i) for j in range(b + 1) for c in range(m - j + 1)
            for i in range(weight - j * d + 1)]


def section_rows(mons, weight, z, q, b):
    powers = [ppow(q, k) for k in range(b + 1)]
    rows = [[0] * len(mons) for _ in range(weight + 1)]
    for col, (j, c, i) in enumerate(mons):
        zc = pow(z, c, P)
        for k, value in enumerate(powers[j]):
            rows[i + k][col] = (rows[i + k][col] + zc * value) % P
    return rows


def line_rows(mons, m, x, line, order):
    """Vanishing of F and, for order two, of F_X and F_Y on the received line
    Y = line(Z) over X = x, as identities in Z."""
    powers = [ppow(line, k) for k in range(max(j for j, _, _ in mons) + 1)]
    blocks = [(0, 0)] if order == 1 else [(0, 0), (1, 0), (0, 1)]
    rows = []
    for dx, dy in blocks:
        block = [[0] * len(mons) for _ in range(m + 1)]
        for col, (j, c, i) in enumerate(mons):
            if i < dx or j < dy:
                continue
            factor = (i if dx else 1) * (j if dy else 1) % P
            factor = factor * pow(x, i - dx, P) % P
            for k, value in enumerate(powers[j - dy]):
                block[c + k][col] = (block[c + k][col] + factor * value) % P
        rows.extend(block)
    return rows


def build_instance(seed, b, m, d, weight, n_sections, n_double, n_simple, n_free):
    rng = random.Random(seed)
    sites = rng.sample(range(1, P), n_double + n_simple + n_free)
    double, simple = sites[:n_double], sites[n_double:n_double + n_simple]
    head_a, head_b = rand_poly(rng, d), rand_poly(rng, d)
    vanisher = [1]
    for x in double:
        vanisher = pmul(vanisher, [(-x) % P, 1])
    scalars = rng.sample(range(1, P), n_sections)
    sections = []
    for z in scalars:
        q = padd(padd(head_a, pscale(head_b, z)),
                 pmul(vanisher, rand_poly(rng, d - n_double)))
        check(deg(q) <= d, 'section degree')
        sections.append((z, q))
    u0, u1 = {}, {}
    for x in double:
        u0[x], u1[x] = peval(head_a, x), peval(head_b, x)
    for index, x in enumerate(simple):
        (z1, q1), (z2, q2) = sections[index % n_sections], \
            sections[(index + 1) % n_sections]
        slope = (peval(q1, x) - peval(q2, x)) * pow(z1 - z2, P - 2, P) % P
        u1[x] = slope
        u0[x] = (peval(q1, x) - z1 * slope) % P
    for x in sites[n_double + n_simple:]:
        u0[x], u1[x] = rng.randrange(P), rng.randrange(P)
    mons = monomials(b, m, d, weight)
    rows = []
    for z, q in sections:
        rows.extend(section_rows(mons, weight, z, q, b))
    for x in double:
        rows.extend(line_rows(mons, m, x, [u0[x], u1[x]], 2))
    for x in simple:
        rows.extend(line_rows(mons, m, x, [u0[x], u1[x]], 1))
    basis = nullspace(rows, len(mons))
    check(len(basis) >= 2, 'the linear system leaves a pencil of surfaces')
    vector = [0] * len(mons)
    for vec in basis:
        c = rng.randrange(1, P)
        vector = [(a + c * v) % P for a, v in zip(vector, vec)]
    coeff = {}
    for value, (j, c, i) in zip(vector, mons):
        poly = coeff.setdefault((j, c), [0] * (weight - j * d + 1))
        poly[i] = value
    coeff = {key: trim(poly) for key, poly in coeff.items()}
    surface = Surface(b, m, d, weight, coeff)
    return surface, sections, sites, double, simple, u0, u1


def run(seed, b, m, d, weight, n_sections, n_double, n_simple, n_free):
    surface, sections, sites, double, simple, u0, u1 = build_instance(
        seed, b, m, d, weight, n_sections, n_double, n_simple, n_free)
    check(any(surface.coeff.get((b, c)) for c in range(m - b + 1)),
          'the value degree is exactly b')
    core = set(double) | set(simple)
    heights = []
    regular_total = singular_regular = 0
    agreements = []
    for z, q in sections:
        check(surface.on_section(z, q) == [], 'the section lies on the surface')
        g = surface.on_section(z, q, dy=1)
        numerator = pscale(surface.on_section(z, q, dz=1), P - 1)
        check(g != [], 'the section is simple')
        common = pgcd(g, numerator) if numerator else g
        den = pdivmod(g, common)[0]
        num = pdivmod(numerator, common)[0] if numerator else []
        height = max(deg(den), deg(num) - d, 0)
        heights.append(height)
        agree = [x for x in sites
                 if peval(q, x) == (u0[x] + z * u1[x]) % P]
        agreements.append(len(agree))
        failures = 0
        for x in agree:
            if x not in core:
                continue
            if peval(den, x) == 0:
                failures += 1
                continue
            value = peval(num, x) * pow(peval(den, x), P - 2, P) % P
            check(value == u1[x], 'the tangent slope takes the second row')
            check((peval(q, x) - z * value) % P == u0[x],
                  'the tangent head takes the first row')
            regular_total += 1
            if x in double:
                check(peval(g, x) == 0, 'F_Y vanishes on a double line')
                singular_regular += 1
        check(failures <= height, 'failures are bounded by the height')
        # On these generic instances the zeros of F_Y on the section are the
        # double lines and the poles of V, and nothing else.
        check(height == weight - d - len(double),
              'height equals W - d minus the number of double lines')
        if b == 2:
            f0, f1, f2 = (surface.y_coefficient(z, j) for j in range(3))
            disc = psub(pmul(f1, f1), pscale(pmul(f2, f0), 4))
            check(disc == pmul(g, g), 'discriminant is the square of F_Y')
    bx = (2 * b - 2) * m - b * (b - 1) + 1
    bz = (2 * b - 2) * weight - b * (b - 1) * d + 1
    budget = 2 * bx * bz + b * (weight * (m - b) + m * (weight - b * d))
    check(sum(heights) <= budget, 'height budget')
    n, t = len(sites), min(agreements)
    if t * t > n * d:
        cap = bx + (m * n * (2 * t + n) + 2 * budget * (t + n)) // (t * t - n * d)
        check(len(sections) <= cap, 'Theorem D-prime')
    return {'seed': seed, 'b': b, 'heights': heights, 'budget': budget,
            'regular': regular_total, 'regular_on_double_lines': singular_regular,
            'min_agreements': t, 'sites': n}


CASES = (
    # seed, b, m, d, weight, sections, double lines, simple lines, free sites
    (1, 2, 3, 5, 30, 5, 3, 6, 4),
    (2, 2, 3, 5, 30, 5, 3, 6, 4),
    (3, 2, 4, 6, 28, 6, 4, 6, 4),
    (4, 3, 4, 4, 26, 4, 2, 6, 4),
    (5, 3, 4, 4, 26, 4, 3, 5, 4),
)


if __name__ == '__main__':
    for case in CASES:
        result = run(*case)
        print(result)
    print(f'{CHECKS} explicit checks passed')
