#!/usr/bin/env python3
"""Check the four-head order-32 occupation and first-prime endpoint arithmetic."""
from itertools import product
from math import comb


def site_charges():
    for values in product(range(4), repeat=4):
        blocks = {v: values.count(v) for v in set(values)}
        pairs = sum(comb(b, 2) for b in blocks.values())
        for choice in range(5):
            matched = blocks.get(choice, 0)
            fresh = len(blocks) if not matched else int(matched < 4)
            charge = 2*matched + fresh
            assert charge <= 4+pairs
            if sorted(blocks.values()) == [2, 2]:
                assert charge <= 4+pairs-1
            if len(blocks) == 4 and matched:
                assert charge == 4+pairs-1
        assert 8 <= 4+pairs+4
        if pairs:
            assert 8 <= 4+pairs+3


def endpoints():
    n = 2**30
    s = n // 32
    d = n // 4 - 1
    e = 480_946_858
    t = n-e
    assert 3*(t-1) == 53*s-1
    assert 3*n+42*s-6-6*(t-1) == n-4
    assert 2*(e+1)+1 <= n-4
    third_population = (n+1-2*(e+1)+1)//2
    lower_core = t - e//(third_population-1)
    uncovered = n - 3*lower_core + 3*d
    assert 1+4*uncovered <= n
    rich_core = t - e//2047
    assert 32+4*(n-3*rich_core+3*d)+2047 < n
    required = 8*(t-1)+n+1
    for m in range(7):
        assert 4*n+6*m*s+4*(8*s-2-m*s) < required
    assert required > 173*s-6
    assert 3*(174*s-8-required) == 2*s-19
    for triples in range(15):
        doubles = 42-3*triples
        ordinary = 32-doubles-triples
        if min(doubles, ordinary) < 0:
            continue
        if ordinary == 0:
            assert triples == 5
        else:
            assert triples >= 6
            high_core = (2*doubles+3*triples)*s + 4*(s-2)
            assert high_core <= 70*s-8
    assert 3*(4*(t-1)-(70*s-8)) == 2*s+20
    print("production", n, s, "three-head cap", n-4,
          "required charge", required,
          "singleton requirements differ by", ((2*s+20)-(2*s-19))//3)


if __name__ == "__main__":
    site_charges()
    endpoints()
