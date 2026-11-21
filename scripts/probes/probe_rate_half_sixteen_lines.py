"""Check rate-half list budget three at length 16 over the 130-bit prime.

Theorem and derivation of the projective lines are in docs/research/proximity-gap/PROGRESS.md.
The program uses only exact arithmetic in the prime field.
"""

from itertools import combinations
from math import prod

P = (3 * 2**48 + 69) * 2**80 + 1
G = pow(5, (P - 1) // 16, P)
DOMAIN = tuple(pow(G, j, P) for j in range(16))
PAIRS = tuple(combinations(range(5), 2))
PROJECTED = tuple(combinations(range(4), 2))
SUPPORTS = tuple((sum(1 << j for j in e), e) for e in combinations(range(16), 5))


def dihedral_orbit(support):
    return {tuple(sorted((a * j + b) % 16 for j in support))
            for a in (1, -1) for b in range(16)}


def lines_over(tmask, support):
    for emask, error in SUPPORTS:
        common = tmask & emask
        if common.bit_count() > 1:
            continue
        seam = common.bit_length() - 1
        u, v = [], []
        for i in support:
            if i == seam:
                u.append(0)
                v.append(1)
                continue
            value = prod(DOMAIN[i] - DOMAIN[j] for j in error if j != seam) % P
            u.append(pow(value, -1, P))
            v.append(DOMAIN[i] * u[-1] % P if seam < 0 else 0)
        minors = tuple((u[i] * v[j] - u[j] * v[i]) % P for i, j in PROJECTED)
        dual = (minors[5], -minors[4], minors[3], minors[2], -minors[1], minors[0])
        yield emask, u, v, minors, dual


def coordinates_on_line(u, v):
    i, j = next((i, j) for i, j in PAIRS if (u[i]*v[j] - u[j]*v[i]) % P)
    pivot = (u[i] * v[j] - u[j] * v[i]) % P

    def residual(z):
        a = (z[i] * v[j] - z[j] * v[i]) % P
        b = (u[i] * z[j] - u[j] * z[i]) % P
        return tuple((pivot*z[k] - a*u[k] - b*v[k]) % P
                     for k in range(5) if k != i and k != j)

    return i, j, residual


def check_fixed_support(tmask, support):
    lines = list(lines_over(tmask, support))
    torus_intersections = coincident_pairs = 0
    for index, (emask, u, v, _, dual) in enumerate(lines):
        i, j, residual = coordinates_on_line(u, v)
        a, b, c, d, e, f = dual
        points = {}
        coincident = []
        for fmask, s, t, minors, _ in lines[index + 1:]:
            if (emask & fmask).bit_count() > 1:
                continue
            l, m, n, o, p, q = minors
            if (a*l + b*m + c*n + d*o + e*p + f*q) % P:
                continue
            restrictions = list(zip(residual(s), residual(t)))
            first = next(((j, -i) for i, j in restrictions if i or j), None)
            if first is None:
                coincident.append(fmask)
                coincident_pairs += 1
                continue
            alpha, beta = first
            if any((alpha*x + beta*y) % P for x, y in restrictions):
                continue
            w = [(alpha*x + beta*y) % P for x, y in zip(s, t)]
            if 0 in w:
                continue
            torus_intersections += 1
            key = w[i] * pow(w[j], -1, P) % P
            points.setdefault(key, []).append(fmask)
        for hits in [coincident, *(group + coincident for group in points.values())]:
            for fmask, gmask in combinations(hits, 2):
                if (fmask & gmask).bit_count() <= 1:
                    raise AssertionError((tmask, emask, fmask, gmask))
    return torus_intersections, coincident_pairs


def check_all():
    if len(set(DOMAIN)) != 16 or pow(G, 16, P) != 1:
        raise AssertionError("wrong order")
    seen = set()
    orbit_count = hits = coincident = 0
    for mask, support in SUPPORTS:
        if support in seen:
            continue
        seen.update(dihedral_orbit(support))
        matched, same = check_fixed_support(mask, support)
        hits += matched
        coincident += same
        orbit_count += 1
    if (len(seen), orbit_count, hits, coincident) != (4368, 147, 3218, 29):
        raise AssertionError((len(seen), orbit_count, hits, coincident))
    print(f"support_orbits={orbit_count} point_intersections={hits} coincident_pairs={coincident}")


def check_radius_six():
    parameters = [DOMAIN[j] for j in (0, 1, 3, 7)]
    seams = {pow(a*b, -1, P) for a, b in combinations(parameters, 2)}
    if len(seams) != 6 or not seams <= set(DOMAIN):
        raise AssertionError("six distinct pairwise intersections required")
    other = [x for x in DOMAIN if x not in seams]
    roots, private = other[:6], other[6:]
    heads = [[prod(x-r for r in roots) * (a*x + pow(a, -1, P)) % P for x in DOMAIN]
             for a in parameters]
    w = []
    for j, x in enumerate(DOMAIN):
        if x in private:
            w.append(heads[private.index(x)][j])
        else:
            values = [head[j] for head in heads]
            w.append(next(v for v in values if values.count(v) >= 2))
    counts = [sum(x == y for x, y in zip(w, head)) for head in heads]
    if counts != [10, 10, 10, 10]:
        raise AssertionError(counts)
    print(f"n=16 k=8 radius_six_agreements={counts}")


if __name__ == "__main__":
    check_radius_six()
    check_all()
