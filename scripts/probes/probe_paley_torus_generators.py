"""Finite checks of Paley walk moments averaged over split and nonsplit generators."""

from collections import Counter
from functools import cache
from itertools import product
from math import comb, gcd, prod

from probe_paley_translate_moments import trace_power


def multiply(f, g, p):
    result = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            result[i + j] = (result[i + j] + a * b) % p
    return result


def scalar_times_square(f, p):
    """Read the monic square root from its leading coefficients, in odd characteristic."""
    if (len(f) - 1) % 2:
        return False
    reverse = [c * pow(f[-1], -1, p) % p for c in reversed(f)]
    root = [1]
    for k in range(1, (len(f) + 1) // 2):
        inner = sum(root[j] * root[k - j] for j in range(1, k))
        root.append((reverse[k] - inner) * pow(2, -1, p) % p)
    return multiply(root, root, p) == reverse


def check(p, delta, rows, cols, r):
    # A=(a,b) acts by multiplication by a+b*sqrt(delta).
    parameters = [(a, 1) for a in range(p)] + [(1, 0)]
    square = [0] + [1 if pow(z, (p - 1) // 2, p) == 1 else -1 for z in range(1, p)]
    group = [(a, b) for a, b in parameters if (a * a - delta * b * b) % p]
    m = len(group)
    diameter = max(*rows, *cols)
    assert m == p - square[delta] and 0 < diameter < min(m, p)

    def action(g, v):
        a, b = g
        x, y = v
        return ((a * x + b * delta * y) % p, (b * x + a * y) % p)

    def bracket(v, w):
        return (v[0] * w[1] - v[1] * w[0]) % p

    def iterates(g, start):
        vertices = [start]
        for _ in range(diameter):
            vertices.append(action(g, vertices[-1]))
        return vertices

    def canonical(v):
        a, b = v
        return (a * pow(b, -1, p) % p, 1) if b else (1, 0)

    def signs(vertices):
        return [[square[bracket(vertices[i], vertices[j])] for j in cols] for i in rows]

    def order(g):
        v = (1, 0)
        for k in range(1, m + 1):
            v = action(g, v)
            if v[1] == 0:
                return k
        raise AssertionError("torus order")

    start = (1, 0)
    second_start = action(next(g for g in group if g[1]), start)
    traces = []
    matrices = []
    generator = []
    for g in group:
        raw = iterates(g, start)
        matrices.append(signs(raw))
        trace = trace_power(signs(list(map(canonical, raw))), r)
        assert trace == trace_power(signs(iterates(g, second_start)), r)
        assert trace >= 0
        traces.append(trace)
        generator.append(order(g) == m)
    assert sum(generator) == sum(gcd(k, m) == 1 for k in range(m))
    assert any(order(g) < diameter for g in group)

    # U_d(a) is the sqrt(delta) coefficient of (a+sqrt(delta))^d, on the b=1 chart.
    u = {d: [comb(d, d - j) * pow(delta, (d - j - 1) // 2, p) % p
             if (d - j) % 2 else 0 for j in range(d)] for d in range(1, diameter + 1)}
    for g in group:
        a, b = g
        if not b:
            continue
        raw = iterates(g, start)
        for i in rows:
            for j in cols:
                if i == j:
                    continue
                d = abs(i - j)
                value = sum(c * pow(a, k, p) for k, c in enumerate(u[d])) % p
                value *= (1 if j > i else -1) * pow(a * a - delta, min(i, j), p)
                assert value % p == bracket(raw[i], raw[j])

    @cache
    def odd_obstruction(odd_distances, determinant_parity):
        polynomial = [(-delta) % p, 0, 1] if determinant_parity else [1]
        for d in odd_distances:
            polynomial = multiply(polynomial, u[d], p)
        return not scalar_times_square(polynomial, p)

    walked = [0] * m
    exceptional = ordinary = zero = larger_even = 0
    for row in product(range(len(rows)), repeat=r):
        for col in product(range(len(cols)), repeat=r):
            edges = [(row[(k + offset) % r], col[k]) for k in range(r) for offset in (0, 1)]
            distances = Counter(abs(rows[i] - cols[j]) for i, j in edges)
            if 0 in distances:
                zero += 1
                continue
            values = [prod(matrix[i][j] for i, j in edges) for matrix in matrices]
            for index, value in enumerate(values):
                walked[index] += value
            odd = tuple(sorted(d for d, count in distances.items() if count % 2))
            if odd:
                ordinary += 1
                larger_even += max(distances) > max(odd)
                parity = sum(min(rows[i], cols[j]) for i, j in edges) % 2
                assert odd_obstruction(odd, parity)
                # Complete on the rational affine chart, including singular parameters.
                affine = 0
                for a in range(p):
                    raw = iterates((a, 1), start)
                    affine += prod(square[bracket(raw[rows[i]], raw[cols[j]])] for i, j in edges)
                distinct_bound = 2 + sum(distances)
                assert affine**2 <= (distinct_bound - 1)**2 * p
            else:
                exceptional += 1

    assert traces == walked
    n = min(len(rows), len(cols))
    large = max(len(rows), len(cols))
    paired_cap = prod(range(1, 2 * r, 2)) * 2**r * n * large**r
    assert exceptional <= paired_cap
    generator_sum = sum(t for t, is_generator in zip(traces, generator) if is_generator)
    assert 0 <= generator_sum <= sum(traces)
    excess = max(0, sum(traces) - m * exceptional - 3 * ordinary)
    assert excess**2 <= (ordinary * (2 * r * diameter + 1))**2 * p
    return zero, ordinary, exceptional, larger_even


def main():
    total = [0, 0, 0, 0]
    cases = 0
    for p in (11, 13, 17, 23):
        nonsquare = next(z for z in range(2, p) if pow(z, (p - 1) // 2, p) == p - 1)
        for delta in (1, nonsquare):
            for rows, cols, r in [((0, 2, 4), (1, 2, 3, 5), 2), ((0, 2, 5), (1, 3, 7), 3)]:
                counts = check(p, delta, rows, cols, r)
                total = [a + b for a, b in zip(total, counts)]
                cases += 1
    assert all(total)
    print(f"{cases} torus/template cases, {total[0]} zero-edge walks, "
          f"{total[1]} nonsquare walks, {total[2]} paired walks; "
          f"{total[3]} nonsquare walks with an even larger distance")


if __name__ == "__main__":
    main()
