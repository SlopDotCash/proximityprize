"""Check the first-prime septic equality module and its sharp deformation distance."""

from itertools import combinations, islice
from math import prod

from probe_rate_half_seven_twenty_fourths import G, N, P, PARTITIONS


def value(coefficients, x):
    result = 0
    for coefficient in reversed(coefficients):
        result = (x * result + coefficient) % P
    return result


def derivative(coefficients):
    return [power * c % P for power, c in enumerate(coefficients) if power]


def nullspace(matrix):
    rows = [row.copy() for row in matrix]
    size = len(rows[0])
    pivots = []
    for column in range(size):
        r = len(pivots)
        pivot = next((i for i in range(r, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inverse = pow(rows[r][column], -1, P)
        rows[r] = [v * inverse % P for v in rows[r]]
        for i, row in enumerate(rows):
            scale = row[column]
            if i != r and scale:
                rows[i] = [(u - scale * v) % P for u, v in zip(row, rows[r])]
        pivots.append(column)
    basis = []
    for column in sorted(set(range(size)) - set(pivots)):
        vector = [0] * size
        vector[column] = 1
        for i, j in enumerate(pivots):
            vector[j] = -rows[i][column] % P
        basis.append(vector)
    return basis


def quotient_basis(degree, nodes):
    rows = []
    width = degree + 1
    for y, partition in zip(nodes, PARTITIONS):
        for digits in partition:
            block = tuple(map(int, digits))
            for i, j in zip(block, block[1:]):
                rows.append([((int(h == i) - int(h == j)) * pow(y, a, P)) % P
                             for h in (1, 2, 3) for a in range(width)])
    assert len(rows) == 28
    return [[[0] * width] + [v[k:k + width] for k in range(0, len(v), width)]
            for v in nullspace(rows)]


def proportional(a, b):
    return all((a[i] * b[j] - a[j] * b[i]) % P == 0
               for i, j in combinations(range(4), 2))


def test_small(n, f, g, ratios):
    """Build a sharp deformation using honest lifted polynomials on all n sites."""
    s = n // 16
    z = pow(G, N // n, P)
    sites = [pow(z, j, P) for j in range(n)]
    fibers = [j % 16 for j in range(n)]
    erasures = [i for i, j in enumerate(fibers) if j in (0, 1)]
    erasures += list(islice((i for i, j in enumerate(fibers) if j == 2), 2))
    erased = {sites[i] for i in erasures}
    assert len(erased) == 2 * s + 2
    centers = [sites[i] for i in erasures]
    divided = [-ratios[fibers[i]] % P for i in erasures]
    for k in range(1, len(centers)):
        for i in range(len(centers) - 1, k - 1, -1):
            divided[i] = ((divided[i] - divided[i - 1])
                          * pow(centers[i] - centers[i - k], -1, P)) % P

    def interpolant(x):
        v, dv = 0, 0
        for i in range(len(centers) - 1, -1, -1):
            dv = (dv * (x - centers[i]) + v) % P
            v = (v * (x - centers[i]) + divided[i]) % P
        return v, dv

    failed = set()
    for x, j in zip(sites, fibers):
        y = pow(x, s, P)
        a, da = interpolant(x)
        fv = [value(c, y) for c in f]
        numer = [(a * u + value(c, y)) % P for u, c in zip(fv, g)]
        if x in erased:
            assert numer == [0] * 4
            shift = s * pow(x, s - 1, P) % P
            numer = [(da * u + shift * (a * value(derivative(v), y)
                                        + value(derivative(w), y))) % P
                     for u, v, w in zip(fv, f, g)]
            denominator = prod((x - h) % P for h in erased if x != h) % P
        else:
            denominator = prod((x - h) % P for h in erased) % P
        heads = [u * pow(denominator, -1, P) % P for u in numer]
        if any(len({heads[int(i)] for i in block}) > 1 for block in PARTITIONS[j]):
            failed.add(x)
    assert failed == erased
    print(f"length {n}: all {len(failed)} prescribed erasures realized")


def main():
    omega = pow(G, N // 16, P)
    nodes = [pow(omega, j, P) for j in range(16)]
    bases = {d: quotient_basis(d, nodes) for d in range(6, 12)}
    dims = [len(bases[d]) for d in range(6, 12)]
    assert dims == [0, 1, 2, 3, 5, 8]
    f = bases[7][0]
    fv = [[value(c, y) for c in f] for y in nodes]
    assert all(any(row) for row in fv)
    g = next(b for b in bases[10] if any(
        not proportional(row, [value(c, y) for c in b]) for row, y in zip(fv, nodes)))
    at_seven = [(value(a, nodes[7]), value(b, nodes[7])) for a, b in zip(f, g)]
    for (x, y), (z, w), (u, v) in combinations(at_seven, 3):
        assert ((z - x) * (v - y) - (u - x) * (w - y)) % P
    ratios = {}
    for j, y in enumerate(nodes):
        row = fv[j]
        gv = [value(c, y) for c in g]
        if not proportional(row, gv):
            continue
        i = next(k for k in range(4) if row[k])
        q = gv[i] * pow(row[i], -1, P) % P
        ratios[j] = q
        slopes = [(value(derivative(b), y) - q * value(derivative(a), y)) % P
                  for a, b in zip(f, g)]
        for a, b in combinations(range(4), 2):
            if row[a] == row[b]:
                assert slopes[a] != slopes[b]
    assert set(ratios) == set(range(16)) - {3, 7, 11}
    for n in (64, 256):
        test_small(n, f, g, ratios)
    s = N // 16
    assert (2 * s + 2, 3 * s + 1) == (134217730, 201326593)
    low = 3 * s + 2
    first = (6 * low + 8 * N - 15 + 31) // 32
    assert first == 306184192
    assert 6 * low > 32 * (first - 1) - 8 * N + 15
    print(f"four-head deformations through {3 * s + 1} are safe through {first - 1} errors")
    print(f"kernel dimensions degrees 6..11: {dims}")
    print(f"actual first-prime length {N}: sharp distance {2 * s + 2}")


if __name__ == "__main__":
    main()
