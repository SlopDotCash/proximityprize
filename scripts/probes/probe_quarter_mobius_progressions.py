#!/usr/bin/env python3
"""Check the mixed-polar fiber bound and the first-prime rotation exclusion."""
from collections import Counter
from itertools import combinations_with_replacement


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def multiply(f, g, p):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i+j] = (out[i+j] + a*b) % p
    return out


def binary_vanisher(roots, p):
    """Coefficients in increasing X-degree, including the Z-factor at infinity."""
    out = [1]
    for r in roots:
        out = multiply(out, [1, 0] if r is None else [-r, 1], p)
    return out


def fourth(f, p):
    square = multiply(f, f, p)
    return multiply(square, square, p)


def mixed_polar(f, p):
    n = len(f) - 1
    return [i*(n-i)*f[i] % p for i in range(1, n)]


def scaled_controls():
    p, n = 17, 16
    sites = list(range(1, p))
    forms = []
    for roots in combinations_with_replacement([None, *range(p)], 2):
        f = binary_vanisher(roots, p)
        values = [pow(f[0] + f[1]*x + f[2]*x*x, 4, p) for x in sites]
        forms.append((roots, fourth(f, p), values))

    successes = Counter()
    for roots_p, p4, values_p in forms:
        for roots_q, q4, values_q in forms:
            if set(roots_p) & set(roots_q):
                continue
            # Multiplicative fourth powers have four distinct values over F_17.
            for scale in (1, 4, 13, 16):
                holes = [x for x, a, b in zip(sites, values_p, values_q)
                         if scale*a % p != b]
                if len(holes) != n-8:
                    continue
                k = binary_vanisher(holes, p)
                left = mixed_polar(multiply(k, p4, p), p)
                right = mixed_polar(multiply(k, q4, p), p)
                require(any(left) and [scale*a % p for a in left] == right,
                        "mixed partial identity")
                central = set(roots_p + roots_q)
                r = 4 - len(central)
                b = len(central & {None, 0})
                h = len(central & set(holes))
                require(2*r+b+h <= n-2-8, "ramification budget")
                successes[r, b, h] += 1
    require(any(r and b and h for r, b, h in successes), "nontrivial local cases")
    return sum(successes.values()), max(2*r+b+h for r, b, h in successes)


def named_cutoffs():
    n = 2**30
    d = n//4-2
    p = n*(2**128+192)+1
    require(p % 3 == 2 and p > n, "separability and conjugate central targets")
    require((n-2-2*d)//4 == 134217728, "cubic central ramification")
    require(n-2-4*d == 6 and 2*d-3 == 536870905, "harmonic central ramification")
    require(d > 3960117 and 4*d <= n < 8*d, "subgroup and target orbit bounds")
    source_orders = [2**j for j in range(2, 31) if d % (2**j//4) == 0]
    require(source_orders == [4, 8], "source rotations")
    require(d % 4 == 2 and 2*(2*(d % 8-1))+2 > 6, "local-index exclusions")
    half_triangle = n//4-1
    require(half_triangle % 4 == 3 and 4*half_triangle <= n < 8*half_triangle,
            "half-successor orbit")
    require(2*(2*(half_triangle % 4-1))+2 > n-2-4*half_triangle == 2,
            "half-successor central ramification")
    m = n//8
    ell = m//4
    require(d//2 == m-1 and (m-1) % 4 == 3, "quotient degree")
    # Both differences are affine in s. Checking the two endpoints covers the interval.
    for s in (0, ell-1):
        require(4*s+1 < m and 2*ell+2*s > 4*s, "quotient differential contradiction")


if __name__ == "__main__":
    named_cutoffs()
    total, maximum = scaled_controls()
    print(f"Verified {total:,} scaled harmonic pencils; maximum local charge {maximum}/6.")
    print("Production central ramification caps and both possible source rotations verified.")
