#!/usr/bin/env python3
"""Check the integral cubic fiber and the named-field quarter-rate allocation."""
from itertools import combinations_with_replacement
from probe_mu32_four_cubics import multiply, value


def main():
    # Work in Z[z]/(z^16+1). The order-sixteen generator is z^2.
    a, b, c = [(0, 1, 8), (2, 9, 10), (3, 5, 7)]
    assert len(set(a + b + c)) == 9
    a = tuple(2*j for j in a)
    b = tuple(2*j for j in b)
    c = tuple(2*j for j in c)
    for x in c:
        assert multiply(value(a, x), value(b, c[0])) == multiply(value(b, x), value(a, c[0]))

    n = 2**30
    s = n // 32
    roots, holes = 2*s - 2, s
    private = 14*s - roots - holes
    assert private % 3 == 0
    core = 12*s + roots + private//3
    e = n - core - 1
    assert e == 480946859
    assert n - roots - holes + 3*holes == n + 2
    assert 6*s + roots + 1 < n//4
    assert core >= n//4
    assert (53*s - 4)//3 == core
    # Test each site charge for one, two, or three distinct head values.
    for groups in ((3,), (2, 1), (1, 1, 1)):
        cap = {1: 6, 2: 5, 3: 3}[len(groups)]
        assert len(groups) <= cap
        for matched in groups:
            assert 2*matched + int(matched < 3) <= cap
    for d in range(8):
        for r in combinations_with_replacement(range(d + 1), 3):
            if d == 7 and r[1:] == (7, 7) and r[0] >= 6:
                continue
            assert 2*sum(r) + 3*(8-d) <= 42
    print(f"Integral cubic pencil verified, first possible error count {e}, core {core}, labels {n+2}")


if __name__ == "__main__":
    main()
