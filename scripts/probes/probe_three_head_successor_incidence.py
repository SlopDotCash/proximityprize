#!/usr/bin/env python3
"""Verify the production three-head predecessor bounds on arbitrary injective domains."""
from math import comb

from probe_tangent_polar_windows import component_price

N = 2**30
# Error count, degree, and method that excludes the selected outside witnesses.
CELLS = (
    (715827880, 71582789, "strict"),
    (715827879, 71582791, "opposite"),
    (715827878, 73688167, "mixed"),
    (715827877, 76695849, "fourth"),
    (715827876, 77650736, "fourth"),
    (715827875, 77686750, "fourth"),
    (715827874, 77734912, "fourth"),
    (715827873, 77768621, "fourth"),
    (715827872, 77782878, "fourth"),
    (715827871, 77807385, "fourth"),
)


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify_cell(e, d, method):
    t = N-e
    c = t-1
    needed = 2*N+1-3*(e+1)
    cutoff = 500000
    core = t-e//(cutoff-1)
    surplus = sum((26-j)*(2*t-j*d) for j in range(8))-77*N
    check(surplus > 0 and 2*t > 7*d and t*t > N*d, "interpolation")
    price = max(component_price(b, 25, 2*t-1, t, d, 0, 0) for b in range(2, 8))
    check(price <= cutoff, "nonlinear factors")
    check(t-25*N//cutoff-3*(25*N//(cutoff-25)) > d, "affine factor")
    check(4*core > N+4*d and 2*(e+1)+5*cutoff+25 <= 2*N, "head classification")
    for j in range(3, 8):
        den = core+(j-1)*d
        union = max(j*core-comb(j, 2)*d, (j*core*core+den-1)//den)
        check(j*N-(j-1)*union+(7-j)*cutoff+25 <= 2*N, "collinear union")
    check(2*(2*N+1-2*(e+1)-4*cutoff-25) > N, "three saturated heads")

    sites = N-3*c+2*d
    tau = t-3*d
    if method == "strict":
        check(sites+3*d < t, "outside agreement cap")
        return surplus, price
    take = 9 if method == "opposite" else needed
    if 3*tau <= 2*sites+d:
        h = take*tau//sites
        slope = comb(h, 2)
        intercept = h*slope-comb(h, 3)
        for w in range(take+1):
            check(slope*w <= comb(w, 3)+intercept, "moment supporting line")
        check(comb(take, 3)*d+sites*intercept < slope*take*tau, "popular triple")
        check(5*tau > 3*sites+2*d, "outside witnesses lie on the triple's line")
    check(2*tau-sites > 4*cutoff+25, "loss when the fourth head is collinear")
    c4 = N+4*d-3*c
    if method == "fourth":
        check(take*t > N+(take-1)*c4, "fourth-head fresh slots")
    else:
        m = 10 if method == "opposite" else take
        face = (0, 0, 2, 5, 8)
        for j in range(4):
            for b in range(2):
                for y in ((m,) if b else (0, 1)):
                    check(4*y+(4*m-2)*j <= 4*m+2*(m-1)*max(0, j-1)
                          +2*j*y+(m-1)*face[j+b], "mixed inequality")
        check(4*m*t+(4*m-2)*3*c > 4*m*N+4*(m-1)*d+6*m*d+8*(m-1)*d,
              "mixed fourth-head obstruction")
        if method == "opposite":
            check(17*3*c+18*t-12*N-51*d > 6*(N+4*d-1), "four-core equality")
            check(9*(t-c4)-3*(c-2*d) == 15 > 9, "repeated opposite label")
    return surplus, price


if __name__ == "__main__":
    for e, d, method in CELLS:
        surplus, price = verify_cell(e, d, method)
        print(f"e={e} k={d+1} method={method} surplus={surplus} nonlinear_cap={price}")
