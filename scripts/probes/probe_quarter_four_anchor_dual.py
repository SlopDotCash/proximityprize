#!/usr/bin/env python3
"""Exact four-anchor rank certificate for the first quarter-rate production field."""

from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt

from probe_quarter_first_resonant_collisions import (
    D, GROUP, N, PRELIMINARY, R, initial_band, intersection, order_floor, require,
)

ORDER = 5_000_000
CAP = 2_525_000
SAFE_ERRORS = 540_186_851


def hit(q):
    """Probability that at least one of four independent anchors hits."""
    return 1 - (1 - q) ** 4


def prices(q):
    """Tangent coefficients for hit(q) as a function of q squared."""
    derivative = 4 * (1 - q) ** 3
    return hit(q) - q * derivative / 2, derivative / (2 * q)


@dataclass(frozen=True)
class RankResult:
    dimension: int
    nullity: int
    degree: int
    split_bound: int


def rank_certificate(errors):
    s = F(N - errors, N)
    require(F(61, 125) <= s < F(1, 2), "quartic primary agreement")
    initial_band(s)
    require(PRELIMINARY > int(ORDER * s / R) + 5 * CAP, "quotient Bezout")

    weights = (5 * R, 6 * R)
    orders = [order_floor(w, ORDER, CAP, s) for w in weights]
    # Intersection is affine and the order floor is concave in w.
    excess = max(intersection(w, 4, 5) + 7 - 4*z for w, z in zip(weights, orders))
    margin = min(s*z - w for w, z in zip(weights, orders))
    require(excess > 0 and margin > 0, "positive excess and separation")
    require(margin**2 > (excess + F(1, 4)) * (R - s*s + (s-R)/1000),
            "fewer than 1000 exterior words")

    eta = R - s*s + (1 + excess)/GROUP
    grid = 10**6
    q = F(isqrt(int(eta/excess * grid**2)), grid)
    upper = q + F(1, grid)
    require(0 < q < upper < 1 and q*q <= eta/excess < upper*upper,
            "tangency frequency bracket")
    price, moment = prices(q)
    # The price increases and the moment coefficient decreases throughout
    # this bracket, so this also proves high-class feasibility at sqrt(eta/J).
    require(3*price*prices(upper)[1] >= 4, "high-length class majorant")
    require(4*(1-s)**3 <= 2*moment*s, "decreasing rank for true-hit mean >= s")
    sampling = (6 + 10*excess)/GROUP
    dimension = 5 + int(N*(hit(s) + price*excess + moment*eta + sampling))
    nullity = GROUP - dimension
    require(nullity > 1, "positive cofactor nullity")
    degree = (GROUP-1)//(nullity-1)
    require(6*D*GROUP**2 < 2**157 and D**2 < 2**157, "characteristic")
    require(s*N > F(N, GROUP) + F(GROUP-1, GROUP-2)*D, "stationary Riccati case")
    return RankResult(dimension, nullity, degree, 62*degree + 5)


if __name__ == "__main__":
    result = rank_certificate(SAFE_ERRORS)
    require(result == RankResult(GROUP-257_988, 257_988, 4161, 257_987), "endpoint")
    require(result.nullity + 1 > result.split_bound, "moving branch excluded")
    adjacent = rank_certificate(SAFE_ERRORS + 1)
    require(adjacent == RankResult(GROUP-257_967, 257_967, 4162, 258_049), "adjacent")
    require(adjacent.nullity + 1 <= adjacent.split_bound, "adjacent bound inconclusive")
    print(f"First-prime quarter-rate list safety through {SAFE_ERRORS:,} errors.")
    print(f"Endpoint: {result}\nNext error: {adjacent}")
