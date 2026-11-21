#!/usr/bin/env python3
"""Classify three disjoint quintic fibers on the sixteenth roots of unity.

Runs with the Python standard library. All coefficients and norms are exact.
The representative of zeta satisfies zeta^8 = -1.
"""
from collections import Counter
from itertools import combinations
from math import comb, gcd

from probe_power_fiber_endpoint import actual_bad_set, evaluate


def multiply(a, b):
    """Negacyclic product in Z[Y]/(Y^len(a)+1)."""
    n = len(a)
    product = [0] * n
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j < n:
                product[i + j] += x * y
            else:
                product[i + j - n] -= x * y
    return tuple(product)


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def shift(a):
    return (-a[-1],) + a[:-1]


def norm(a):
    """Eliminate Y over Y^2 at each step of the cyclotomic tower."""
    while len(a) > 1:
        even, odd = a[::2], a[1::2]
        a = subtract(multiply(even, even), shift(multiply(odd, odd)))
    return abs(a[0])


def vanisher(indices):
    one = (1,) + (0,) * 7
    zero = (0,) * 8
    coefficients = [one]
    for i in indices:
        root = tuple((1 if i < 8 else -1) if j == i % 8 else 0
                     for j in range(8))
        coefficients = [subtract(x, multiply(root, y)) for x, y in
                        zip([zero] + coefficients, coefficients + [zero])]
    return coefficients[:-1]  # all leading coefficients are one


def mask(indices):
    return sum(1 << i for i in indices)


def partitions():
    sites = range(1, 16)  # scaling sends the unique omitted site to 1
    full = mask(sites)
    for tail in combinations(range(2, 16), 4):
        a = mask((1,) + tail)
        other = [i for i in sites if not (a >> i) & 1]
        for tail_b in combinations(other[1:], 4):
            b = mask((other[0],) + tail_b)
            yield tuple(sorted((a, b, full ^ a ^ b)))


def representatives():
    five_sets = list(combinations(range(1, 16), 5))
    conjugates = {mask(s): [mask((t * i) % 16 for i in s)
                            for t in range(1, 16, 2)] for s in five_sets}
    seen = set()
    for triple in partitions():
        if triple in seen:
            continue
        orbit = {tuple(sorted(conjugate))
                 for conjugate in zip(*(conjugates[s] for s in triple))}
        seen.update(orbit)
        yield triple, len(orbit)
    total = comb(15, 5) * comb(10, 5) // 6
    if len(seen) != total:
        raise ArithmeticError("incomplete partition orbit cover")


def minor_polynomials(forms):
    a, b, c = forms
    u = [subtract(x, y) for x, y in zip(a, b)]
    v = [subtract(x, y) for x, y in zip(a, c)]
    for i, j in combinations(range(5), 2):
        yield subtract(multiply(u[i], v[j]), multiply(u[j], v[i]))


def prime_factors(n):
    p = 3
    while p * p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        yield n


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def polynomial_gcd(a, b, p):
    a, b = trim([x % p for x in a]), trim([x % p for x in b])
    while b:
        inv = pow(b[-1], -1, p)
        while len(a) >= len(b):
            scale = a[-1] * inv % p
            start = len(a) - len(b)
            for j, x in enumerate(b):
                a[start + j] = (a[start + j] - scale * x) % p
            trim(a)
        a, b = b, a
    inv = pow(a[-1], -1, p)
    return [x * inv % p for x in a]


def check_smooth_seventeen():
    # Coefficients in ascending degree for P and (V/B) mod P in the pencil.
    sites = list(range(1, 17))
    denominator = (11, 5, 11, 14, 4, 1)
    weight = (15, 10, 3, 12, 12)
    ratio = {x: evaluate(weight, x, 17) * pow(evaluate(denominator, x, 17), -1, 17)
             % 17 for x in sites}
    rows = ({x: x * ratio[x] % 17 for x in sites}, {x: -ratio[x] % 17 for x in sites})
    bad = actual_bad_set(sites, rows, 8, 4, 17)
    if bad != set(range(2, 17)):
        raise ArithmeticError(f"unexpected actual bad scalar set: {bad}")
    print("F_17, smooth n=16, k=8, e=4: bad scalars are exactly 2 through 16")


def main():
    forms = {mask(s): vanisher(s) for s in combinations(range(1, 16), 5)}
    candidates = Counter()
    count = covered = 0
    incidences = Counter()
    witnesses = {}
    for triple, multiplicity in representatives():
        count += 1
        covered += multiplicity
        common = 0
        chosen = [forms[i] for i in triple]
        for minor in minor_polynomials(chosen):
            n = norm(minor)
            if n:
                odd = n // (n & -n)
                common = gcd(common, odd)
                if common == 1:
                    break
        if not common:
            raise ArithmeticError(f"characteristic-zero pencil: {triple}")
        candidates[common] += multiplicity
        for p in prime_factors(common):
            root_poly = [1] + [0] * 7 + [1]
            for minor in minor_polynomials(chosen):
                root_poly = polynomial_gcd(root_poly, minor, p)
            degree = len(root_poly) - 1
            incidences[p] += multiplicity * degree
            if degree and p not in witnesses:
                witnesses[p] = (triple, root_poly)
    print(f"{covered} unordered partitions in {count} Galois orbits")
    print("odd gcds of minor norms, weighted by orbit size:", sorted(candidates.items()))

    # Every primitive root gives the same count because odd powers permute the sites.
    for p, weighted in sorted(incidences.items()):
        number, remainder = divmod(weighted, 8)
        if remainder:
            raise ArithmeticError("asymmetric primitive-root count")
        print(f"characteristic {p}: {number} partitions at a fixed primitive root")
        if number:
            triple, root_poly = witnesses[p]
            blocks = [[i for i in range(1, 16) if (s >> i) & 1] for s in triple]
            print(f"  witness exponents {blocks}, root gcd coefficients {root_poly}")


if __name__ == "__main__":
    main()
    check_smooth_seventeen()
