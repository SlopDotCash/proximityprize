#!/usr/bin/env python3
"""Exact component and joint-core budgets for three production MCA windows."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement

N = 2**30


@dataclass(frozen=True)
class Window:
    rate: int
    errors: int
    outer: tuple[int, int, int]
    secondary: tuple[int, int, int]
    kappa: Fraction


WINDOWS = (
    Window(2, 299_100_000, (7, 9, 31973), (12, 17, 109), Fraction(912, 1000)),
    Window(4, 514_400_000, (6, 11, 6594), (11, 22, 110), Fraction(832, 1000)),
    Window(8, 665_600_000, (4, 12, 1729), (8, 24, 85), Fraction(757, 1000)),
)


def require(ok, why):
    if not ok:
        raise ValueError(why)


def monomial_surplus(shape, t, d):
    r, v, s = shape
    cols = sum((s-j+1)*max(0, r*t-j*d) for j in range(v+1))
    rows = N*sum((r-j)*(s+1-j) for j in range(r))
    return cols - rows


def checked_bound(window):
    e = window.errors
    d = N//window.rate-1
    t = N-e
    r, v, s = window.outer
    _, va, a = window.secondary
    K = window.kappa
    ranks = tuple(monomial_surplus(z, t, d) for z in (window.outer, window.secondary))
    require(min(ranks) > 0, "nonzero interpolants")
    cutoff = max(e//256 + 1, s*va+v*a+1)
    # All populations above the cutoff lie on a common irreducible factor.
    # A value-linear one gives a head by the identity-site argument.
    require(t-a*N//cutoff-3*(a*N//(cutoff-a)) > d, "affine-head test")
    c = t-255
    group = 3 if 3*c > N+2*d else 4
    require(group == 3 or 4*c > N+4*d, "rich-head determinant")
    den = (5*K**4-4*K**5)*t-d
    require(0 < K <= 1 and den > 0 and 5 <= 2*K*(2+2), "weighted moment signs")

    def caps(b, j, degree):
        if b == 1:
            return cutoff
        w = r*t-1-(degree-b)*d
        m = a-j
        if w < b*d or m < b:
            return cutoff
        bx = (2*b-2)*m-b*(b-1)+1
        bz = (2*b-2)*w-b*(b-1)*d+1
        require(bx > 0 and bz > 0, "discriminant bounds")
        cost = 2*K**5*b*(4*m*bx*bz + m*N + bx*bz) + (N-d)*(m+1)
        return max(cutoff, bx + cost//den)

    def affine_mass(j):
        if j < group:
            return j*(e+1)
        divisor = c+(j-1)*d
        covered = (j*c*c + divisor-1)//divisor
        return min(j*(e+1), j*N-(j-1)*covered)

    worst = (-1, ())
    checked = 0
    for j in range(v+1):
        for count in range(v-j+1):
            for degrees in combinations_with_replacement(range(1, v-j+1), count):
                degree = j+sum(degrees)
                if degree > v:
                    continue
                bounded = affine_mass(j)+sum(caps(b, j, degree) for b in degrees)
                checked += 1
                if bounded > worst[0]:
                    worst = (bounded, (j, degrees))
    require(worst[0] <= 2*N, "production scalar budget")
    return ranks, cutoff, checked, worst


if __name__ == "__main__":
    for w in WINDOWS:
        print(w.rate, w.errors, checked_bound(w))
