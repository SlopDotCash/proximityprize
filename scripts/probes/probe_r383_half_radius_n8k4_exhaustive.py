#!/usr/bin/env python3
"""Find a proper-ball counterexample for RS[8,4] over the dyadic F_17 domain.

At the half-radius predecessor e = 3, each support span is a projective hyperplane
in the four-dimensional syndrome space.  A point of a projective line is MCA-bad
exactly when it lies in one of the 56 support hyperplanes that does not contain the
whole line. Hyperplane-incidence bitmasks make the complete 89,030-line search small.
The probe succeeds when the complete traversal finds a line with more than n
proper points.
"""

from itertools import combinations, product


P = 17
N = 8
K = 4
E = N // 2 - 1
D = N - K


def primitive_root(p):
    factors = []
    x = p - 1
    q = 2
    while q * q <= x:
        if x % q == 0:
            factors.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        factors.append(x)
    return next(g for g in range(2, p)
                if all(pow(g, (p - 1) // q, p) != 1 for q in factors))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % P


def add_scaled(a, scalar, b):
    return tuple((x + scalar * y) % P for x, y in zip(a, b))


def normalize(v):
    pivot = next(x for x in v if x)
    inv = pow(pivot, P - 2, P)
    return tuple(inv * x % P for x in v)


def null_vector(rows):
    """Return the normalized generator of a one-dimensional right kernel."""
    a = [list(row) for row in rows]
    pivots = []
    row = 0
    for col in range(D):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inv = pow(a[row][col], P - 2, P)
        a[row] = [inv * x % P for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                scale = a[i][col]
                a[i] = [(x - scale * y) % P for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
    assert row == D - 1
    free = next(col for col in range(D) if col not in pivots)
    v = [0] * D
    v[free] = 1
    for i, pivot in enumerate(pivots):
        v[pivot] = -a[i][free] % P
    return normalize(v)


def projective_points():
    for pivot in range(D):
        for suffix in product(range(P), repeat=D - pivot - 1):
            yield (0,) * pivot + (1,) + suffix


def projective_lines_rref():
    """Unique RREF bases for all two-planes in F_17^4."""
    for first in range(D - 1):
        for second in range(first + 1, D):
            free_first = [j for j in range(first + 1, D) if j != second]
            free_second = list(range(second + 1, D))
            for values in product(range(P), repeat=len(free_first) + len(free_second)):
                a = [0] * D
                b = [0] * D
                a[first] = 1
                b[second] = 1
                cut = len(free_first)
                for j, value in zip(free_first, values[:cut]):
                    a[j] = value
                for j, value in zip(free_second, values[cut:]):
                    b[j] = value
                yield tuple(a), tuple(b)


def setup_masks():
    omega = pow(primitive_root(P), (P - 1) // N, P)
    domain = [pow(omega, i, P) for i in range(N)]
    columns = [tuple(pow(x, j, P) for j in range(D)) for x in domain]
    supports = list(combinations(range(N), E))
    normals = [null_vector([columns[i] for i in support]) for support in supports]
    points = list(projective_points())
    masks = {
        point: sum(1 << index for index, normal in enumerate(normals)
                   if dot(normal, point) == 0)
        for point in points
    }
    return domain, columns, supports, masks


def solve_on_support(point, support, columns):
    """Solve point as a linear combination of three independent columns."""
    matrix = [[columns[index][row] for index in support] + [point[row]]
              for row in range(D)]
    pivot_row = 0
    for col in range(E):
        pivot = next(i for i in range(pivot_row, D) if matrix[i][col])
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        inv = pow(matrix[pivot_row][col], P - 2, P)
        matrix[pivot_row] = [inv * x % P for x in matrix[pivot_row]]
        for i in range(D):
            if i != pivot_row and matrix[i][col]:
                scale = matrix[i][col]
                matrix[i] = [(x - scale * y) % P
                             for x, y in zip(matrix[i], matrix[pivot_row])]
        pivot_row += 1
    assert all(not any(row[:E]) and row[E] == 0 for row in matrix[pivot_row:])
    return tuple(matrix[i][E] for i in range(E))


def line_bad_points(a, b, masks):
    joint_mask = masks[a] & masks[b]
    points = [normalize(add_scaled(a, gamma, b)) for gamma in range(P)] + [b]
    bad = [point for point in points if masks[point] & ~joint_mask]
    return points, bad, joint_mask


def run():
    domain, columns, supports, masks = setup_masks()
    best = (0, None)
    found_counterexample = False
    histogram = {}
    total = 0
    for a, b in projective_lines_rref():
        total += 1
        points, bad, joint_mask = line_bad_points(a, b, masks)
        score = len(bad)
        histogram[score] = histogram.get(score, 0) + 1
        if score > best[0]:
            witnesses = []
            for point in bad:
                proper_mask = masks[point] & ~joint_mask
                support_index = (proper_mask & -proper_mask).bit_length() - 1
                support = supports[support_index]
                witnesses.append({
                    "point": point,
                    "support": support,
                    "domain_points": tuple(domain[i] for i in support),
                    "coefficients": solve_on_support(point, support, columns),
                })
            best = (score, {
                "basis": (a, b),
                "points": points,
                "bad_points": bad,
                "joint_supports": [i for i in range(len(supports))
                                   if joint_mask >> i & 1],
                "witnesses": witnesses,
            })
            print({"line": total, "new_best": best}, flush=True)
        if score > N:
            if not found_counterexample:
                print("COUNTEREXAMPLE", best, flush=True)
            found_counterexample = True
    expected_lines = P ** 4 + P ** 3 + 2 * P ** 2 + P + 1
    assert total == expected_lines
    print({
        "field": P,
        "n": N,
        "k": K,
        "e": E,
        "domain": domain,
        "projective_points": len(masks),
        "support_hyperplanes": len(supports),
        "projective_lines": total,
        "best": best,
        "histogram": histogram,
    })
    if not found_counterexample:
        print("NO COUNTEREXAMPLE FOUND", flush=True)
    return found_counterexample


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
