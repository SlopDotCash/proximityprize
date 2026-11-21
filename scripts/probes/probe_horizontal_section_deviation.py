#!/usr/bin/env python3
"""Exact section and head counts at half rate on the second production prime."""
from fractions import Fraction
from math import isqrt

from probe_weighted_hodge_windows import N, monomial_surplus


def upper_square_root(num, den):
    root = isqrt(num // den)
    return root if root * root * den == num else root + 1


def component_price(b, weight, degree, t, d):
    bx = (2*b - 2)*degree - b*(b - 1) + 1
    bz = (2*b - 2)*weight - b*(b - 1)*d + 1
    assert bx > 0 and bz > 0
    exceptions = (N-d)*(degree+1)
    # The chord through 7/50 and 43/50 forces an intermediate site.
    chord = (2500-301)*t - 301*N - 2500*d
    assert chord > 0
    no_middle = 2500*exceptions // chord
    # 2 * (7/50) * (1-14/50) = 126/625.
    middle = upper_square_root(625*b*degree*bx*bz, 126) + (50*(degree+bx)+6)//7
    across_sections = max(no_middle, middle)
    # The per-section estimate is stronger on some low-degree components.
    kappa = Fraction(457, 500)
    moment = (5*kappa**4 - 4*kappa**5)*t - d
    assert moment > 0 and 5 <= 2*kappa*(b+2)
    variance = b * (2*degree*bx*(bz-1) + degree*N)
    across_sites = (2*kappa**5*variance + exceptions) // moment
    return bx + min(across_sections, across_sites)


def certificate():
    errors = 302_850_000
    d, t = N//2 - 1, N-errors
    primary, companion = (9, 12, 2_092_862), (17, 24, 185)
    r, v, s = primary
    _, v2, a = companion
    surpluses = tuple(monomial_surplus(shape, t, d) for shape in (primary, companion))
    assert min(surpluses) > 0
    cutoff = max(errors//256+1, s*v2+v*a+1)
    assert t-a*N//cutoff-3*(a*N//(cutoff-a)) > d
    core = t-255
    assert 3*core > N+2*d
    worst = (-1, None)
    for j in range(v+1):
        heads = j*(errors+1)
        if j >= 3:
            denom = core+(j-1)*d
            covered = (j*core**2+denom-1)//denom
            heads = min(heads, j*N-(j-1)*covered)
        for l in range(j, v+1):
            prices = [0, cutoff]
            for b in range(2, l-j+1):
                weight, degree = r*t-1-(l-b)*d, a-j
                price = component_price(b, weight, degree, t, d) if weight >= b*d and degree >= b else 0
                prices.append(max(cutoff, price))
            best = [0]
            for slots in range(1, l-j+1):
                best.append(max(prices[b]+best[slots-b] for b in range(1, slots+1)))
            value = s + heads + best[-1]
            if value > worst[0]:
                worst = value, (j, l)
    assert worst[0] <= 2*N
    return surpluses, cutoff, worst


if __name__ == '__main__':
    print(certificate())
