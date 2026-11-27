"""Check the two-error MCA pencils and actual received rows on smooth octagons."""

from itertools import combinations, product
from math import prod


def locator(points, p):
    coefficients = [1]
    for x in points:
        new = [0] * (len(coefficients) + 1)
        for j, value in enumerate(coefficients):
            new[j] -= x * value
            new[j + 1] += value
        coefficients = [v % p for v in new]
    return coefficients


def projective(row, p):
    inverse = pow(next(v for v in row if v % p), -1, p)
    return tuple(v * inverse % p for v in row)


def line_points(u, v, p):
    yield projective(v, p)
    for t in range(p):
        yield projective([x + t * y for x, y in zip(u, v)], p)


def exhaustive_two_errors(xs, p):
    """Enumerate syndrome lines in reduced echelon form, independent of cubic pencils."""
    columns = [tuple(pow(x, j, p) for j in range(4)) for x in xs]
    secant_points = set()
    secants = set()
    for u, v in combinations(columns, 2):
        points = frozenset(line_points(u, v, p))
        secants.add(points)
        secant_points.update(points)

    maximum = total = 0
    for i, j in combinations(range(4), 2):
        free = [(0, t) for t in range(i + 1, 4) if t != j]
        free += [(1, t) for t in range(j + 1, 4)]
        for values in product(range(p), repeat=len(free)):
            rows = [[0] * 4 for _ in range(2)]
            rows[0][i] = rows[1][j] = 1
            for (row, col), value in zip(free, values):
                rows[row][col] = value
            points = frozenset(line_points(*rows, p))
            hits = 2 if points in secants else len(points & secant_points)
            maximum = max(maximum, hits)
            total += 1
    assert total == (p * p + 1) * (p * p + p + 1)
    return maximum, total


def rref(matrix, p):
    rows = [row[:] for row in matrix]
    pivots = []
    for col in range(len(rows[0])):
        i = len(pivots)
        pivot = next((j for j in range(i, len(rows)) if rows[j][col] % p), None)
        if pivot is None:
            continue
        rows[i], rows[pivot] = rows[pivot], rows[i]
        inv = pow(rows[i][col], -1, p)
        rows[i] = [x * inv % p for x in rows[i]]
        for j in range(len(rows)):
            if j != i:
                rows[j] = [(x - rows[j][col] * y) % p for x, y in zip(rows[j], rows[i])]
        pivots.append(col)
        if len(pivots) == len(rows):
            break
    return rows, pivots


def syndrome_preimage(syndrome, xs, p):
    weights = [pow(prod(x - y for y in xs if y != x), -1, p) for x in xs[:4]]
    equations = [[w * pow(x, j, p) % p for x, w in zip(xs, weights)] + [s]
                 for j, s in enumerate(syndrome)]
    rows, pivots = rref(equations, p)
    assert pivots == list(range(4))
    return [row[-1] for row in rows] + [0] * 4


def actual_bad_labels(u, v, xs, p):
    """Interpolate both received rows on each support of size at least six."""
    labels = set()
    for size in (6, 7, 8):
        for support in combinations(range(8), size):
            anchors = support[:4]
            residuals = []
            for j in support[4:]:
                coeffs = [prod((xs[j] - xs[b]) * pow(xs[a] - xs[b], -1, p)
                               for b in anchors if b != a) % p for a in anchors]
                residuals.append(tuple((row[j] - sum(c * row[a] for c, a in zip(coeffs, anchors))) % p
                                       for row in (u, v)))
            direction = next(((x, y) for x, y in residuals if y), None)
            if direction:
                x, y = direction
                label = -x * pow(y, -1, p) % p
                if all((a + label * b) % p == 0 for a, b in residuals):
                    labels.add(label)
    return labels


def pencil_witness(p):
    z = next(pow(a, (p - 1) // 8, p) for a in range(2, p)
             if pow(a, (p - 1) // 2, p) == p - 1)
    xs = tuple(pow(z, j, p) for j in range(8))
    assert len(set(xs)) == 8
    pairs = []
    for a in combinations(xs, 3):
        for b in combinations([x for x in xs if x not in a], 3):
            if a >= b:
                continue
            u, v = set(xs) - set(a) - set(b)
            def value(s, x):
                return prod(x - t for t in s) % p
            if (value(a, u) * value(b, v) - value(a, v) * value(b, u)) % p == 0:
                pairs.append((a, b))
    a, b = pairs[0] if pairs else (xs[:3], xs[3:6])
    rows, pivots = rref([locator(a, p), locator(b, p)], p)
    basis = []
    for j in sorted(set(range(4)) - set(pivots)):
        vector = [0] * 4
        vector[j] = 1
        for row, i in zip(rows, pivots):
            vector[i] = -row[j] % p
        basis.append(syndrome_preimage(vector, xs, p))
    u, v = basis
    expected = 7 if pairs else 6
    # Move the missing projective point away from all labels.
    for s in range(expected + 1):
        direction = [(x + s*y) % p for x, y in zip(u, v)]
        labels = actual_bad_labels(v, direction, xs, p)
        if len(labels) == expected:
            return xs, len(pairs), sorted(labels)
    raise AssertionError("the affine chart lost a crossing for every choice")


def main():
    ordinary = 387 * 2**122 + 1
    assert pow(13, (ordinary - 1) // 2, ordinary) == ordinary - 1
    assert 387 < 2**122 and ordinary // 2**128 == 17**32 // 2**128 == 6
    for p, count in [(17, 7), (41, 6), (ordinary, 6)]:
        xs, partitions, labels = pencil_witness(p)
        assert len(labels) == count
        print(f"F_{p}: {partitions} partitions into 3+3+2, {count} actual bad scalars")
        if p == 17:
            maximum, lines = exhaustive_two_errors(xs, p)
            assert maximum == count
            print(f"F_17: maximum {maximum} on all {lines} projective syndrome lines")


if __name__ == "__main__":
    main()
