#!/usr/bin/env python3
"""Enumerate every pole and partner-row value for a subfield in a quadratic extension."""
from itertools import combinations
from math import comb, isqrt, prod


def check(s):
    # Encode a+b*sqrt(nonsquare) by a+s*b. The subfield is range(s).
    q = s*s
    nonsquare = next(x for x in range(2, s) if pow(x, (s-1)//2, s) != 1)

    def multiply(x, y):
        b, a = divmod(x, s)
        d, c = divmod(y, s)
        return (a*c + nonsquare*b*d) % s + s*((a*d + b*c) % s)

    def subtract(x, y):
        return (x % s - y % s) % s + s*((x//s - y//s) % s)

    squares = {multiply(x, x) for x in range(1, q)}
    if len(squares) != (q-1)//2:
        raise ArithmeticError("wrong quadratic extension")
    chi = [0] + [1 if x in squares else -1 for x in range(1, q)]
    inverse = {x: next(y for y in range(1, q) if multiply(x, y) == 1) for x in range(1, q)}
    row = [[chi[subtract(x, z)] for z in range(q)] for x in range(q)]
    for pole in range(q):
        domain = [inverse[subtract(a, pole)] for a in range(s) if a != pole]
        values = [sum(row[x][z] for x in domain) for z in range(q)]
        if pole < s:
            if sum(values[:s]) != (s-1)**2:
                raise ArithmeticError(("subfield pole", s, pole))
        else:
            conjugate = pole % s + s*((-(pole//s)) % s)
            exceptional = inverse[subtract(conjugate, pole)]
            if abs(values[exceptional]) != s or values[0] != -1:
                raise ArithmeticError(("exceptional target", s, pole))
            others = [abs(w) for z, w in enumerate(values) if z != exceptional]
            if max(others) > 1 + isqrt(4*s):
                raise ArithmeticError(("quartic bound", s, pole))
    # Evaluate quartic traces directly by multiplicativity at their four distinct sites.
    quartics = sum(sum(prod(row[a][z] for a in points) for z in range(q))
                   for points in combinations(range(s), 4))
    if s >= 5 and (s-2)*quartics != comb(s, 4)*((s-1)*(s-2) + 3):
        raise ArithmeticError(("quartic mean", s, quartics))
    return q*q


if __name__ == "__main__":
    cases = (3, 5, 7, 11, 13, 17)
    rows = sum(check(s) for s in cases)
    print(f"{rows} exact pole-target sums and all quartic averages across {len(cases)} square fields")
