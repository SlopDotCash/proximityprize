#!/usr/bin/env python3
"""Exhaust RS[8,4]/F_17 syndrome lines at error weight two.

This is the one-extra-agreement version of the R383 rate-1/2 counterexample:
agreement six rather than five.  It tests whether the rate-1/4 large-core
branch could inherit more than eight outside rich points after puncturing to
an eight-coordinate complement.
"""

from itertools import combinations

from probe_r383_half_radius_n8k4_exhaustive import (
    N,
    P,
    add_scaled,
    normalize,
    primitive_root,
    projective_lines_rref,
    projective_points,
)


D = 4
E = 2


def setup_masks():
    omega = pow(primitive_root(P), (P - 1) // N, P)
    domain = [pow(omega, i, P) for i in range(N)]
    columns = [tuple(pow(x, j, P) for j in range(D)) for x in domain]
    supports = list(combinations(range(N), E))
    masks = {point: 0 for point in projective_points()}
    for index, (i, j) in enumerate(supports):
        a, b = columns[i], columns[j]
        span_points = [normalize(add_scaled(a, gamma, b))
                       for gamma in range(P)] + [normalize(b)]
        for point in span_points:
            masks[point] |= 1 << index
    return domain, supports, masks


def run():
    domain, supports, masks = setup_masks()
    histogram = {}
    best = (0, None)
    total = 0
    for a, b in projective_lines_rref():
        total += 1
        joint = masks[a] & masks[b]
        points = [normalize(add_scaled(a, gamma, b))
                  for gamma in range(P)] + [normalize(b)]
        bad = [point for point in points if masks[point] & ~joint]
        score = len(bad)
        histogram[score] = histogram.get(score, 0) + 1
        if score > best[0]:
            witnesses = []
            for point in bad:
                proper = masks[point] & ~joint
                index = (proper & -proper).bit_length() - 1
                witnesses.append((point, supports[index]))
            best = (score, {"basis": (a, b), "witnesses": witnesses})
    result = {
        "p": P,
        "n": N,
        "k": 4,
        "e": E,
        "domain": domain,
        "projective_lines": total,
        "best": best,
        "histogram": histogram,
    }
    print(result)
    return best[0] <= N


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
