#!/usr/bin/env python3
"""Bound fixed projective locator families on the named order-64 and order-128 grids."""

from collections import Counter, deque
from itertools import combinations
from math import comb, prod

from probe_mu64_unit_lattice import PRIMES

MODULUS = 257


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def affine_orbit(order, anchors):
    return {
        tuple(sorted(((j - a) * u) % order for j in anchors))
        for a in anchors for u in range(1, order, 2)
    }


def affine_orbits(order, poles):
    """Translate a pole to zero, then quotient by the odd multipliers."""
    seen = set()
    for tail in combinations(range(1, order), poles - 1):
        anchors = (0, *tail)
        if anchors in seen:
            continue
        orbit = affine_orbit(order, anchors)
        require(orbit.isdisjoint(seen), "affine orbits overlap")
        seen.update(orbit)
        yield anchors, orbit
    require(len(seen) == comb(order - 1, poles - 1), "affine orbit census incomplete")


def primitive_exponents(order):
    coordinates = [[0] * (order // 4) for _ in range(order)]
    for index, odd in enumerate(range(1, order // 2, 2)):
        for level in range(order.bit_length() - 1):
            j = (odd << level) % order
            coordinates[j][index] += 1
            coordinates[-j][index] += 1
    return coordinates


def constraint_columns(order, anchors, primitive):
    columns = []
    for j in range(order):
        if j in anchors:
            continue
        base = primitive[(j - anchors[0]) % order]
        column = [1]
        for a in anchors[1:]:
            current = primitive[(j - a) % order]
            column.extend((x - y) % MODULUS for x, y in zip(current, base))
        columns.append(column)
    return columns


def column_basis(columns, indices):
    pivots = {}
    basis = []
    for i in indices:
        values = columns[i].copy()
        for j in sorted(pivots):
            factor = values[j]
            if factor:
                other = pivots[j]
                for k in range(j, len(values)):
                    values[k] = (values[k] - factor * other[k]) % MODULUS
        j = next((k for k, value in enumerate(values) if value), None)
        if j is not None:
            inverse = pow(values[j], -1, MODULUS)
            pivots[j] = [(v * inverse) % MODULUS for v in values]
            basis.append(i)
    return basis


def fundamental_circuits(columns, basis):
    """For each column return its basis support, or None outside the span."""
    rows = list(map(list, zip(*columns)))
    for r, i in enumerate(basis):
        k = next(t for t in range(r, len(rows)) if rows[t][i])
        rows[k], rows[r] = rows[r], rows[k]
        inverse = pow(rows[r][i], -1, MODULUS)
        row = [(v * inverse) % MODULUS for v in rows[r]]
        rows[r] = row
        for k, other in enumerate(rows):
            factor = other[i]
            if k != r and factor:
                rows[k] = [(v - factor * u) % MODULUS for v, u in zip(other, row)]
    return [
        None if any(row[i] for row in rows[len(basis):])
        else [j for j, row in zip(basis, rows) if row[i]]
        for i in range(len(columns))
    ]


def cover_by_two_independent_sets(columns):
    """Augment a pair of independent sets until their union covers all columns."""
    sites = list(range(len(columns)))
    first = column_basis(columns, sites)
    sets = [first, column_basis(columns, [j for j in sites if j not in first])]
    while sum(map(len, sets)) < len(sites):
        unassigned = [j for j in sites if j not in sets[0] and j not in sets[1]]
        circuits = [fundamental_circuits(columns, block) for block in sets]
        parent = dict.fromkeys(unassigned)
        queue = deque(unassigned)
        endpoint = None
        while queue and endpoint is None:
            i = queue.popleft()
            for color, block in enumerate(sets):
                if i in block:
                    continue
                circuit = circuits[color][i]
                if circuit is None:
                    endpoint = (i, color)
                    break
                for j in circuit:
                    if j not in parent:
                        parent[j] = (i, color)
                        queue.append(j)
        require(endpoint is not None, "independent cover not found")
        i, color = endpoint
        sets[color].append(i)
        while parent[i] is not None:
            previous, color = parent[i]
            sets[color].remove(i)
            sets[color].append(previous)
            i = previous
        require(sum(map(len, sets)) == len(sites) - len(unassigned) + 1,
                "augmentation did not add one column")

    information = []
    for block in sets:
        require(len(column_basis(columns, block)) == len(block), "color is dependent")
        basis = column_basis(columns, block + [j for j in sites if j not in block])
        require(len(basis) == len(first), "wrong rank after basis extension")
        information.append(set(sites).difference(basis))
    require(information[0].isdisjoint(information[1]), "information sets overlap")
    return len(information[0])


def lightest_weight(dimension, size):
    total = 0
    for i in range(dimension + 1):
        count = min(comb(dimension, i), size)
        total += i * count
        size -= count
        if not size:
            return total
    raise ValueError("family exceeds the Boolean cube")


def weight_cap(dimension, available, weight, samples=2, maximum_load=1):
    limit = min(weight, available - weight)
    lo, hi = 0, (1 << dimension) + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if samples * lightest_weight(dimension, mid) <= maximum_load * limit * mid:
            lo = mid
        else:
            hi = mid
    return lo


def direct_field_control():
    order, anchors, degree = 16, (0, 4, 8), 6
    sites = [j for j in range(order) if j not in anchors]
    columns = constraint_columns(order, anchors, primitive_exponents(order))
    for p, generator in zip(PRIMES, (3, 37)):
        root = pow(generator, (p - 1) // order, p)
        values = [pow(root, i, p) for i in range(order)]
        require(len(set(values)) == order, "field-control order")
        labels, counts = {}, Counter()
        for subset in combinations(range(len(sites)), degree):
            locators = [prod(values[a] - values[sites[i]] for i in subset) % p
                        for a in anchors]
            inverse = pow(locators[0], -1, p)
            key = tuple(x * inverse % p for x in locators[1:])
            column_sum = tuple(sum(v) % MODULUS for v in zip(*(columns[i] for i in subset)))
            require(labels.setdefault(key, column_sum) == column_sum,
                    "equal projective values violate the displacement equations")
            counts[key] += 1
        require(len(counts) == 1624 and max(counts.values()) == 4,
                "field control missed a repeated projective value")
    print("Both named primes, order 16: 1,716 locators in 1,624 projective classes, maximum 4.")


def main():
    direct_field_control()
    for order, expected in [(64, {28: 30, 29: 5}), (128, {60: 62, 61: 6})]:
        primitive = primitive_exponents(order)
        counts = Counter()
        for anchors, _ in affine_orbits(order, 3):
            columns = constraint_columns(order, anchors, primitive)
            counts[cover_by_two_independent_sets(columns)] += 1
        require(counts == expected, "unexpected triple dimension census")
        print(f"Order {order}, {sum(counts.values())} pole triples up to symmetry, "
              f"two disjoint information sets in each case: {dict(sorted(counts.items()))}")

    primitive = primitive_exponents(64)
    counts = Counter()
    for anchors, _ in affine_orbits(64, 4):
        columns = constraint_columns(64, anchors, primitive)
        dimension = len(columns) - len(column_basis(columns, range(len(columns))))
        counts[dimension] += 1
    require(sum(counts.values()) == 399 and max(counts) == 22,
            "unexpected four-pole rank census")
    print(f"Order 64, {sum(counts.values())} pole quartets up to symmetry, "
          f"largest information set required: {max(counts)}")

    for order, dimension, size, expected in [
            (64, 29, 18, 25_947_093),
            (64, 29, 34, 421_645_935),
            (128, 61, 10, 7_108_458)]:
        cap = weight_cap(dimension, order - 3, size)
        require(cap == expected, "weight cap mismatch")
        print(f"Order {order}, support size {size}: at most {cap:,} projective locators.")


if __name__ == "__main__":
    main()
