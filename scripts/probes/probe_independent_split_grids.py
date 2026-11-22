#!/usr/bin/env python3
"""Certify independent complete bipartite configurations at the named list frontiers."""

from fractions import Fraction as Q
from math import comb, isqrt, prod
from probe_affine_rank_moments import CASES, N, profile


def ceiling(x):
    return -(-x.numerator // x.denominator)


def grid(rate, multiple, errors, missing, left, right):
    t, d, total = N - errors, N // rate - 1, multiple * N + 1
    caps = [1] + [v for v, _ in profile(N, t, d, total)]
    q, rem = divmod(total*t, N)
    pair_hits = N*comb(q, 2) + rem*q
    edges = ceiling(Q(pair_hits - (d-missing-1)*comb(total, 2), missing+1))
    minimum_average = 2 * edges // total
    # Discrete convexity of x -> choose(x,a) gives the lower incidence count.
    all_subsets = comb(total, left)
    dependent = comb(total, left-1) * caps[left-2] if left > 1 else 0
    neighbors = ceiling(Q(total*comb(minimum_average, left) - total*dependent, all_subsets))
    assert neighbors > caps[left+right-2]
    # Work on exactly this many common neighbors. At the j-th draw, at most
    # caps[left+j-1] members of the list belong to the current affine hull.
    independence = prod(Q(neighbors-caps[left+j-1], neighbors-j) for j in range(right))
    assert 0 < independence <= 1
    rho = Q(t, N)
    quadratic = (1-rho**right-right*rho**(right-1)*(1-rho))/(1-rho)**2
    variance = Q(t-d, neighbors) + d - Q(t*t, N)
    assert variance >= 0
    # Every common selected site lies on the first side as well. For one
    # vertex, the centered frequency sum on its support is at most d-t*rho.
    # Two distinct supports meet in at most d sites; use Cauchy there.
    if left == 1:
        expected = t*rho**right + right*rho**(right-1)*(d-t*rho) + quadratic*variance
    else:
        sqrt_bound = isqrt(ceiling(d*variance)) + 1
        expected = d*rho**right + right*rho**(right-1)*sqrt_bound + quadratic*variance
    common = int(expected / independence)
    # A spanning tree joins all words. Each of its edges has at most
    # missing extra agreements, with one further allowance for multiplicity
    # and roots outside the domain.
    gcd = common + (left+right)*missing
    assert gcd < d-missing
    return neighbors, caps[left+right-2], common, gcd


def whole_star_gcd(rate, errors, missing, neighbors):
    t, d = N - errors, N // rate - 1
    rho = Q(t, N)
    variance = Q(t-d, neighbors) + d - Q(t*t, N)
    # Count gcd roots in one edge's chosen root set. Across all neighbors
    # at most 'missing' of those roots may be omitted per support.
    size = 1
    while max(0, size*(1-rho)-missing)**2 <= size*variance:
        size += 1
    # ((1-rho)*sqrt(size)-missing/sqrt(size))_+ is nondecreasing.
    return size - 1 + missing


def primitive_nineteen():
    """The clipped support moments exclude a root common to every 19-tuple."""
    t, d, h = 379625061, 134217727, 765474164
    # The punctured integral pair moment excludes this many supports at one site.
    total_at_site = 682920128
    a, rem = divmod(total_at_site*(t-1), N-1)
    pairs = (N-1)*comb(a, 2) + rem*a
    assert pairs > (d-1)*comb(total_at_site, 2)
    max_load = total_at_site - 2  # Exclude the head from the leaf count.
    rho, high = Q(t, N), Q(max_load, h)
    variance = Q(t-d, h) + d - Q(t*t, N)
    assert 2*(Q(4, 5)-rho)**2 > variance
    assert 18*(Q(1, 2)-rho)**2 > variance
    assert (1+Q(29, 50)-2*rho)**2 > 2*variance
    avoid = h-max_load
    # The leaves omitting a fixed site cannot all contain eight other sites.
    assert avoid*(t-8)**2 > (N-8)*((t-8)+(avoid-1)*(d-8))

    def quad(z):
        return (z**18-rho**18-18*rho**17*(z-rho))/(z-rho)**2

    # At most one site exceeds 4/5. Charge its extra curvature independently.
    low, top = quad(Q(4, 5)), quad(high)
    expected = t*rho**18 + 18*rho**17*(d-t*rho) + low*variance + (top-low)*(high-rho)**2
    rare = 17*7*Q(29, 50)**18
    assert expected < Q(2965, 1000) < 3-rare
    assert rare < Q(66, 10000)
    caps = [1] + [v for v, _ in profile(N, t, d, N+1)]
    assert caps[18] == 155824732 < h
    print(f"first eighth-rate primitive independent leaves=19 neighbors={h} "
          f"uniform_gcd_one_at={max_load+1} max_cover_partners=7")


if __name__ == "__main__":
    full = (12, 15, 0, 0, 9, 5, 5, 6)
    near = (19, 21, 9, 10, 10, 8, 7, 7)
    for (r, b, errors, _, _), a0, a1 in zip(CASES, full, near):
        for missing, side in ((0, a0), (1, a1)):
            if side:
                h, cap, common, gcd = grid(r, b, errors, missing, side, side)
                print(f"1/{r} B={b}n errors={errors} deficit={missing} K_{side},{side} "
                      f"neighbors={h} rank_cap={cap} common_support<={common} gcd<={gcd}")
        star_size = {(2,1):51, (2,2):53, (4,1):26, (4,2):27,
                     (8,1):19, (8,2):18, (16,1):14, (16,2):15}[r,b]
        missing = int(r == 4)
        h, cap, common, gcd = grid(r, b, errors, missing, 1, star_size)
        print(f"star 1/{r} B={b}n deficit={missing} independent_differences={star_size} "
              f"neighbors={h} common_support<={common} gcd<={gcd} "
              f"whole_gcd<={whole_star_gcd(r, errors, missing, h)}")
    primitive_nineteen()
