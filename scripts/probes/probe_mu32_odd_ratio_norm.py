#!/usr/bin/env python3
"""Exact upper bounds on the odd part of a nonzero two-locator comparison norm on μ32."""
from functools import cache
from math import isqrt, prod

N = 32
SCALE = 2**100


def ceil_div(a, b):
    return -(-a//b)


@cache
def twice_cos(n, t):
    """Closed integer enclosure of SCALE times 2*cos(2πt/n), for dyadic n."""
    t %= n
    if n == 2:
        value = (-1 if t else 1)*2*SCALE
        return value, value
    if 4*t in (n, 3*n):
        return 0, 0
    low, high = twice_cos(n//2, t % (n//2))
    low = isqrt(max(0, (2*SCALE+low)*SCALE))
    high = isqrt((2*SCALE+high)*SCALE)+1
    return (-high, -low) if n < 4*t < 3*n else (low, high)


@cache
def chord(t):
    """Closed enclosure of SCALE times |1−ζ^t|, allowing outward rounding."""
    low, high = twice_cos(N, t % N)
    return isqrt(max(0, (2*SCALE-high)*SCALE)), isqrt((2*SCALE-low)*SCALE)+1


def comparison_bound(shift):
    sites = [a for a in range(1, N) if a != shift]
    # Each digit selects zero, one, or two copies of a complex-conjugate embedding.
    rows = []
    for u in range(1, N//2, 2):
        bounds = []
        for a in sites:
            left = chord((u*a) % N)
            right = chord((u*(a-shift)) % N)
            assert min(*left, *right) > 0
            bounds.append((SCALE*left[0]//right[1], ceil_div(SCALE*left[1], right[0])))
        rows.append(bounds)

    total = 0

    def visit(i, low, high, multiplicity):
        nonlocal total
        if i == len(rows):
            # The extremum over equal disjoint sizes 0..15 is at size 15.
            top = prod(sorted(high)[-15:])
            bottom = prod(sorted(low)[:15])
            assert bottom > 0
            total += multiplicity * ceil_div(top, bottom)
            return
        visit(i+1, low, high, multiplicity)
        # Outward fixed-point multiplication keeps each array an enclosure.
        for exponent in (1, 2):
            low = [a*b[0]//SCALE for a, b in zip(low, rows[i])]
            high = [ceil_div(a*b[1], SCALE) for a, b in zip(high, rows[i])]
            visit(i+1, low, high, multiplicity*(2 if exponent == 1 else 1))

    visit(0, [SCALE]*len(sites), [SCALE]*len(sites), 1)
    return total


if __name__ == '__main__':
    # Galois conjugation is transitive on shifts of a fixed two-adic valuation.
    for shift, bits in [(1, 142), (2, 133), (4, 131), (8, 132), (16, 150)]:
        bound = comparison_bound(shift)
        assert 2**(bits-1) < bound < 2**bits
        print(shift, bound, bits, flush=True)
