#!/usr/bin/env python3
"""Compare cyclic-cover Frobenius divisibility with all six-site split pencils in F17."""
from collections import Counter
from itertools import combinations

from probe_split_pencil_square_completions import add, check, locator

P = 17


def projective_class(branch):
    """Normalize an ordered triple to infinity, zero and one and minimize the other labels."""
    representatives = []
    for a in branch:
        for b in branch:
            if b == a:
                continue
            values = [(x-b)*pow(x-a, -1, P) % P for x in branch if x not in (a, b)]
            for c in values:
                inv = pow(c, -1, P)
                representatives.append(tuple(sorted(x*inv % P for x in values)))
    return min(representatives)


def has_pencil(branch):
    pairs = list(combinations(branch, 2))
    for i, fixed in enumerate(pairs):
        base = locator(fixed, P)
        directions = set()
        for other in pairs[i+1:]:
            if set(other).intersection(fixed):
                continue
            diff = add(locator(other, P), base, P, -1)
            inv = pow(diff[-1], -1, P)
            direction = tuple(v*inv % P for v in diff)
            if direction in directions:
                return True
            directions.add(direction)
    return False


def cube_characters(degree):
    """Logarithms modulo three in F17[X]/(X^degree-3), with a checked full generator."""
    order = P**degree

    def multiply(x, y):
        left, right = [], []
        for _ in range(degree):
            left.append(x % P)
            right.append(y % P)
            x //= P
            y //= P
        coeffs = [0] * (2*degree-1)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                coeffs[i+j] += a*b
        for i in range(degree, len(coeffs)):
            coeffs[i-degree] += 3*coeffs[i]
        return sum((coeffs[i] % P)*P**i for i in range(degree))

    def power(x, k):
        value = 1
        while k:
            if k % 2:
                value = multiply(value, x)
            x = multiply(x, x)
            k //= 2
        return value

    factors = (2, 3, 5, 29) if degree == 4 else (2, 3)
    generator = next(x for x in range(P, order)
                     if all(power(x, (order-1)//r) != 1 for r in factors))
    characters = [-1] * order
    x = 1
    for exponent in range(order-1):
        check(characters[x] == -1, "repeated generator orbit")
        characters[x] = exponent % 3
        x = multiply(x, generator)
    check(x == 1 and characters.count(-1) == 1 and characters[0] == -1, "field coverage")
    return characters


def point_count(branch, characters):
    # Three points over infinity for a monic sextic; one over each branch site.
    count = 3 + len(branch)
    for high in range(0, len(characters), P):
        row = characters[high:high+P]
        for low in range(P):
            if high == 0 and low in branch:
                continue
            if sum(row[(low-a) % P] for a in branch) % 3 == 0:
                count += 3
    return count


def main():
    classes = {}
    for branch in combinations(range(1, P), 6):
        key = projective_class(branch)
        if key not in classes:
            classes[key] = [branch, 0, has_pencil(branch)]
        classes[key][1] += 1
    squares, fourths = cube_characters(2), cube_characters(4)
    counts = Counter()
    for branch, size, pencil in classes.values():
        n2, n4 = point_count(branch, squares), point_count(branch, fourths)
        twice_a2 = n2-P**2-1
        check(twice_a2 % 2 == 0, "quadratic count")
        a2 = twice_a2 // 2
        four_a4 = n4-P**4-1+2*a2*a2
        check(four_a4 % 4 == 0, "quartic count")
        divisible = 2*P**2-2*P*a2+four_a4//4 == 0
        counts[pencil, divisible] += size
    check(len(classes) == 10 and counts == {(False, False): 2112, (True, True): 5896},
          "complete six-site comparison")
    print("F17: ten projective classes, 5,896 unions passing both tests, 2,112 failing both.")


if __name__ == "__main__":
    main()
