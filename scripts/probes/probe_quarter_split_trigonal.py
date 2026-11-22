#!/usr/bin/env python3
"""Check the elliptic trace condition for every six-site union in the order-16 subgroup of F17."""
from itertools import combinations, product
from math import comb

P = 17
Q = P**4


def multiply(x, y):
    """Multiply in F17[T]/(T^4-3), using base-17 coefficient digits."""
    left, right = [], []
    for _ in range(4):
        left.append(x % P)
        right.append(y % P)
        x //= P
        y //= P
    coefficients = [0] * 4
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coefficients[(i+j) % 4] += a*b*(3 if i+j >= 4 else 1)
    return sum((a % P)*P**i for i, a in enumerate(coefficients))


def power(x, n):
    result = 1
    while n:
        if n % 2:
            result = multiply(result, x)
        x = multiply(x, x)
        n //= 2
    return result


def cubic_characters():
    order = Q-1
    primes = [2, 3, 5, 29]
    assert order == 2**6 * 3**2 * 5 * 29
    generator = next(g for g in range(P, Q)
                     if all(power(g, order//prime) != 1 for prime in primes))
    character = [-1] * Q
    subfield = {0}
    x = 1
    for i in range(order):
        assert character[x] == -1
        character[x] = i % 3
        if i % (P**2+1) == 0:
            subfield.add(x)
        x = multiply(x, generator)
    assert x == 1 and len(subfield) == P**2
    return character, subfield


def curve_counts(roots, character, subfield):
    """Count the smooth curve's points over F17^2 and F17^4, including infinity."""
    # Three unramified points lie over infinity. Each finite root contributes one.
    n2 = n4 = 3 + len(roots)
    for x in range(Q):
        if x in roots:
            continue
        base, digit = divmod(x, P)
        cubic = sum(character[base*P + (digit-r) % P] for r in roots) % 3 == 0
        if cubic:
            n4 += 3
            if x in subfield:
                n2 += 3
    return n2, n4


def orbit(roots):
    """PGL2 orbit restricted to sets of six finite nonzero sites."""
    images = set()
    for a, b in product(range(1, P), range(P)):
        points = tuple(sorted((a*x+b) % P for x in roots))
        if points[0]:
            images.add(points)
    for a, b, d in product(range(P), repeat=3):
        if (a*d-b) % P == 0 or -d % P in roots:
            continue
        points = tuple(sorted((a*x+b)*pow((x+d) % P, -1, P) % P for x in roots))
        if points[0]:
            images.add(points)
    return images


def partitions(roots):
    if not roots:
        yield []
        return
    for i in range(1, len(roots)):
        for pairs in partitions(roots[1:i] + roots[i+1:]):
            yield [(roots[0], roots[i])] + pairs


def pencil_count(roots):
    count = 0
    for pairs in partitions(roots):
        (a,b), (c,d), (e,f) = [((-x-y) % P, x*y % P) for x, y in pairs]
        count += ((c-a)*(f-b) - (e-a)*(d-b)) % P == 0
    return count


def main():
    character, subfield = cubic_characters()
    remaining = set(combinations(range(1, P), 6))
    excluded = admitted = split = orbit_count = 0
    while remaining:
        representative = min(remaining)
        members = orbit(representative)
        assert members <= remaining
        remaining -= members
        n2, n4 = curve_counts(representative, character, subfield)
        # N1 and N3 equal p^j+1 since cubing is bijective there. The odd
        # Frobenius traces vanish. Newton identities determine a and b.
        trace2, trace4 = P**2+1-n2, P**4+1-n4
        assert trace2 % 2 == 0 and (trace2**2-2*trace4) % 8 == 0
        a, b = -trace2//2, (trace2**2-2*trace4)//8
        obstruction = b-2*P*a+2*P**2
        choices = pencil_count(representative)
        assert all(pencil_count(member) == choices for member in members)
        assert not choices or obstruction == 0
        if obstruction:
            excluded += len(members)
        else:
            admitted += len(members)
        if choices:
            split += len(members)
        orbit_count += 1
        print(representative, len(members), n2, n4, obstruction, choices)
    assert excluded+admitted == comb(16, 6)
    assert (orbit_count, excluded, admitted, split) == (10, 2112, 5896, 5896)
    print(f"{orbit_count} orbits, {excluded} excluded, {admitted} admitted, {split} split")


if __name__ == "__main__":
    main()
