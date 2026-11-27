#!/usr/bin/env python3
"""Verify the polynomial jet derivative recurrence and the two production degree comparisons."""
from collections import Counter
from math import prod


PRIME = 101
ONE = {(0, 0, 0): 1}
Z = {(0, 1, 0): 1}
V = {(0, 0, 1): 1}


def combine(*terms):
    result = Counter()
    for coefficient, polynomial in terms:
        for monomial, value in polynomial.items():
            result[monomial] += coefficient * value
    return {m: c % PRIME for m, c in result.items() if c % PRIME}


def multiply(*polynomials):
    result = ONE
    for polynomial in polynomials:
        terms = Counter()
        for m, c in result.items():
            for n, d in polynomial.items():
                terms[tuple(a+b for a, b in zip(m, n))] += c*d
        result = {m: c % PRIME for m, c in terms.items() if c % PRIME}
    return result


def partial(f, variable):
    derivative = {}
    for powers, c in f.items():
        if powers[variable]:
            m = list(powers)
            m[variable] -= 1
            derivative[tuple(m)] = c*powers[variable] % PRIME
    return derivative


def evaluate(f, point):
    return sum(c*prod(pow(x, e, PRIME) for x, e in zip(point, m))
               for m, c in f.items()) % PRIME


def jet_numerators(g, order):
    t = partial(g, 2)

    def horizontal(f):
        return combine((1, partial(f, 0)), (1, multiply(V, partial(f, 1))))

    b = combine((-1, horizontal(g)))
    dt = combine((1, multiply(t, horizontal(t))), (1, multiply(b, partial(t, 2))))
    numerator = V
    power = 0
    for _ in range(order):
        yield numerator, t, power
        numerator = combine((1, multiply(t, t, horizontal(numerator))),
                            (1, multiply(t, b, partial(numerator, 2))),
                            (-power, multiply(numerator, dt)))
        power += 2


def check_jet(g, points, order):
    for j, (numerator, t, power) in enumerate(jet_numerators(g, order), 1):
        for point, expected in points:
            denominator = evaluate(t, point)
            if evaluate(g, point) or not denominator:
                raise ArithmeticError("Control jet is off the nonsingular differential chart")
            if evaluate(numerator, point) != expected(j) * pow(denominator, power, PRIME) % PRIME:
                raise ArithmeticError(("Derivative mismatch", j, point))


def main():
    # All (X+c)^2 satisfy V^2=4Z and have zero third derivative.
    parabola = combine((1, multiply(V, V)), (-4, Z))
    points = []
    for x in range(PRIME):
        for c in (1, 3, 17):
            y = (x+c) % PRIME
            if y:
                points.append(((x, y*y % PRIME, 2*y % PRIME),
                               lambda j, y=y: 2*y if j == 1 else 2 if j == 2 else 0))
    check_jet(parabola, points, 5)

    # H=sqrt(X) satisfies 2 Z V=1. Its odd branch term survives differentiation.
    sqrt_ode = combine((2, multiply(Z, V)), (-1, ONE))
    points = []
    half = pow(2, -1, PRIME)
    for y in range(1, PRIME):
        x = y*y % PRIME
        points.append(((x, y, pow(2*y, -1, PRIME)),
                       lambda j, y=y: prod(half-i for i in range(j))*pow(y, 1-2*j, PRIME)))
    check_jet(sqrt_ode, points, 6)
    u, s, v, members, rank = 1538, 30, 8, 1072766345, 160
    degree = s+v
    bezout = degree*degree*(1+2*u)
    component = (members+degree-1)//degree
    e = rank*degree*u
    # The hyperelliptic involution has at least 2(n-3080)-(n-4) ramification sites.
    D_floor = (2*(2**30-3080)-(2**30-4)+1)//2
    if not (bezout == 4443188 < 28230694 == component and (2*v-1)*e < D_floor):
        raise ArithmeticError("Production component or resultant degree guard")
    print(f"Derivative controls passed over F{PRIME}. At most {bezout:,} isolated jets "
          f"versus at least {component:,} sections on a component.")
    print(f"The resultant X-degree is at most {(2*v-1)*e:,} against a minimal degree "
          f"of at least {D_floor:,}.")


if __name__ == "__main__":
    main()
