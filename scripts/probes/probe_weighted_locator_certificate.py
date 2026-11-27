"""Exact-arithmetic certificate for the pair-weighted reciprocal-locator radius.

The pair-weighted argument compares two per-triple quantities:

  mean surplus   `(b-2-80003)/(b-2) * ((W(mu) - 100000)/3 - 1)`
  ledger gap     `[n^2 ((n-D) ordered + 2 D b) - g (g-n) (g-2n)] / (n^2 ordered)`

with `W` the tangent minorant of `F(e) = (e-t+l)^3/(4 (e-t)^2) - (D-e)` at the
tangent point `a`, and `mu` the mean pair-union bound produced by the
third-moment ledger.  The argument closes when the mean surplus exceeds the
ledger gap.

This script checks, in exact rational arithmetic:

* the published certificate at `t = 223512374` (round bounds 4000000 / 3800000),
* the successor certificate at `t = 223580000`, where the ledger gap has grown
  to 3898096 and a single round bound 3900000 still separates the two sides,
* the derived mean pair-union bound `mu > 397323129` used by both,
* the radius ceiling of this argument, found by a bounded exact search.

Run: `python3 scripts/probes/probe_weighted_locator_certificate.py [--frontier]`
"""

from __future__ import annotations

import sys
from fractions import Fraction as Q

N = 1073741824
D = 536870913
B = N + 1
ORDERED = B * (B - 1) * (B - 2)
U = (N - D) * ORDERED + 2 * D * B + 3 * N * B * B
JMAX = 20233794


def mu(t: int, q: int) -> Q:
    """Mean pair-union lower bound from the third-moment ledger."""
    g = B * (N - t)
    denom = 3 * q * B * (B - 1)
    return Q(N * denom - 2 * U - N * q ** 3 + 3 * q * g, denom)


def tangent(t: int, a: int):
    """Normalized tangent minorant `W` of `F` at `a`, and the slope numerator."""
    l = D - 2 * t
    s = a - t
    y = 4 * s ** 3
    slope = 5 * s ** 3 - 3 * l * l * s - 2 * l ** 3

    def w(e: int) -> Q:
        return Q(s * (s + l) ** 3 - (D - a) * y + slope * (e - a), y)

    return w, slope, y


def gap(t: int) -> Q:
    """Ledger gap per ordered triple."""
    g = B * (N - t)
    return Q(N * N * ((N - D) * ORDERED + 2 * D * B) - g * (g - N) * (g - 2 * N),
             N * N * ORDERED)


def surplus(t: int, a: int, q: int) -> Q:
    """Mean surplus per unordered triple."""
    w, _, _ = tangent(t, a)
    return Q(B - 2 - 80003, B - 2) * ((w(mu(t, q)) - 100000) / 3 - 1)


def band_ok(t: int, a: int) -> bool:
    """Slope positivity, the two band caps and the locator line cap."""
    l = D - 2 * t
    w, slope, _ = tangent(t, a)
    return (slope > 0 and w(t) < 100000 and w(2 * t) - 100000 < 3 * 20233795
            and N < 16 * l - 8 * JMAX)


def admissible(t: int, q: int) -> int | None:
    """Largest tangent point in the band below the mean bound."""
    a = int(mu(t, q)) - 1
    while a > t:
        if band_ok(t, a):
            return a
        a -= 1
    return None


def max_tangent(t: int, q: int) -> int | None:
    """Largest tangent point satisfying the band caps, by monotone bisection.

    The slope is positive exactly above `D - t`, and the band cap is monotone
    in the tangent point, so the admissible set is an interval.
    """
    lo, hi = max(t + 2, D - t + 2), int(mu(t, q)) - 1
    if hi <= lo or not band_ok(t, lo):
        return None
    if band_ok(t, hi):
        return hi
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if band_ok(t, mid):
            lo = mid
        else:
            hi = mid
    return lo


def check(t: int, a: int, q: int, bound: int) -> dict[str, bool]:
    """The eight certificate conditions at one radius."""
    w, slope, y = tangent(t, a)
    g = B * (N - t)
    denom = 3 * q * B * (B - 1)
    mean_num = N * denom - 2 * U - N * q ** 3 + 3 * q * g
    return {
        "slope > 0": slope > 0,
        "W(t) < 100000 Y": w(t) < 100000,
        "band cap": w(2 * t) - 100000 < 3 * 20233795,
        "line cap": N < 16 * (D - 2 * t) - 8 * JMAX,
        "repeat cap": 17 * 2 * t < 80000 * 100000,
        "mu > 397323129": 397323129 * denom < mean_num,
        f"surplus > {bound}": surplus(t, a, q) > bound,
        f"gap < {bound}": gap(t) < bound,
    }


def report(t: int, a: int, q: int, bound: int) -> bool:
    conditions = check(t, a, q, bound)
    ok = all(conditions.values())
    print(f"t = {t}, a = {a}, q = {q}, bound = {bound}: {'PASS' if ok else 'FAIL'}")
    print(f"  mean pair-union bound mu = {float(mu(t, q)):.3f}")
    print(f"  mean surplus per triple  = {float(surplus(t, a, q)):.3f}")
    print(f"  ledger gap per triple    = {float(gap(t)):.3f}")
    for name, value in conditions.items():
        print(f"  {'ok  ' if value else 'FAIL'} {name}")
    return ok


def frontier(lo: int = 223512374, hi: int = 223620000) -> int:
    """Largest radius whose exact gap the optimized tangent point still clears."""
    q = 852000000
    while lo < hi:
        mid = (lo + hi + 1) // 2
        a = max_tangent(mid, q)
        if a is not None and surplus(mid, a, q) > gap(mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def main() -> int:
    ok = True
    ok &= report(223512374, 397000000, 850229450, 3800000)
    ok &= report(223580000, 397300000, 852000000, 3900000)
    if "--frontier" in sys.argv:
        ceiling = frontier()
        a = max_tangent(ceiling, 852000000)
        print(f"radius ceiling of the argument: {ceiling} (tangent point {a})")
        print(f"  candidate floor (t+1)/2^30 = {ceiling + 1}/{N}")
        ok &= 223590000 < ceiling < 223592000
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
