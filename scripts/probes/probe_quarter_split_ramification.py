#!/usr/bin/env python3
"""Check the two-level norm bounds and all degree-two and three pencils through a fixed fiber in F17."""
from itertools import combinations, product


def locator(roots, p):
    coefficients = [1]
    for root in roots:
        result = [0] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            result[i] = (result[i] - root * coefficient) % p
            result[i + 1] = coefficient
        coefficients = result
    return tuple(coefficients)


def check_pencils(degree):
    p, generator = 17, 3
    nodes = [pow(generator, i, p) for i in range(p - 1)]
    fibers = {locator(roots, p): frozenset(roots) for roots in combinations(nodes, degree)}
    anchor = locator(nodes[:degree], p)
    pencils = set()
    indices = set()
    for second, second_roots in fibers.items():
        if fibers[anchor] & second_roots:
            continue
        for ratio in range(2, p):
            third = tuple((x + ratio * (y-x)) % p for x, y in zip(anchor, second))
            if third not in fibers or (fibers[anchor] | second_roots) & fibers[third]:
                continue
            pencil = tuple(sorted([anchor, second, third]))
            if pencil in pencils:
                continue
            pencils.add(pencil)
            infinity = degree - max(i for i in range(degree) if anchor[i] != second[i])
            zero = min(i for i in range(degree + 1) if (anchor[i]*second[0] - second[i]*anchor[0]) % p)
            indices.add((zero, infinity))
            for exponent in list(range(1, infinity)) + list(range(1-zero, 0)):
                sums = {sum(pow(x, exponent, p) for x in fibers[coefficients]) % p
                        for coefficients in pencil}
                assert len(sums) == 1
            for pair in combinations(pencil, 2):
                left, right = (fibers[coefficients] for coefficients in pair)
                signed = [int(x in left) - int(x in right) for x in nodes]
                folded = [x - y for x, y in zip(signed[:8], signed[8:])]
                assert sum(x*x for x in folded) <= 4*degree
                for exponent in range(1, len(nodes), 2):
                    z = pow(generator, exponent, p)
                    spectral = sum(pow(x, exponent, p) for x in left) - sum(pow(x, exponent, p) for x in right)
                    assert (spectral - sum(x*pow(z, i, p) for i, x in enumerate(folded))) % p == 0
    assert pencils and max(max(pair) for pair in indices) >= 2
    return len(pencils), sorted(indices)


def main():
    for i, j in product(range(4), repeat=2):
        imbalances = [int(i == color) - int(j == color) for color in range(3)]
        assert sum((x-y)**2 for x, y in combinations(imbalances, 2)) <= 3*((i != 3) + (j != 3))
    for degree in [2, 3]:
        count, indices = check_pencils(degree)
        print(f"F17, fixed degree-{degree} fiber: {count} triples, indices {indices}")
    for energy, length, tests, power, bits in [
        (805306362, 268435456, 50263626, 12276, 363185),
        (536870908, 134217728, 24634900, 1, 29),
        (402653181, 134217728, 24282334, 3631, 103792),
    ]:
        assert energy**power < 1 << bits
        assert bits*length <= 158*power*tests
    total = 100527253
    for e in range(1, 5):
        f = total-e
        assert e//2 + f//2 >= 50263626
        assert e//4 + f//4 >= 24634900
    assert 268435454-(total-2) == 167908203
    assert 2*(2*(24282334-1)+2) == 97129336
    print("All three production norm certificates and both ramification bounds passed.")


if __name__ == "__main__":
    main()
