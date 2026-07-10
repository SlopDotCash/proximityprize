#!/usr/bin/env python3
"""Randomized rigidity check for the three-core coexistence identity (m=4).

Three joint cores of size t-1 = 35 for pairwise-distinct pencils over the
64-point smooth domain in F_193 require polynomials A_12, A_23 of degree
<= k-1 = 15 such that A_12, A_23 AND A_13 = A_12 + A_23 each vanish on ~14
domain points (pairwise core overlaps), with the same zero sets carried by
non-proportional slope differences R_ij.

The mu_16 fibre ansatz (cubic potentials) realizes Sum_p - t0 = 40, one short
of the 41 needed for three 35-cores at m=4 (probe_fsmf_p1_onefresh_capacity).
This probe samples random deficiency-one candidates
  A_12 = Z_S(x) * (x - s),  A_23 = lambda * Z_T(x) * (x - u)
(S, T random disjoint 14-subsets of the domain) and counts the domain zeros
of A_13 = A_12 + A_23.  If unstructured triples with >= 13 domain zeros were
common, the coverage wall would be soft; the expected count for a generic
degree-15 polynomial is 15 * 64/193 ~ 5 total roots, of which a domain zero
set of size >= 13 is astronomically unlikely.  Reported: histogram of
|zeros(A_13) cap domain| over trials.

Deterministic seed; pure python + numpy.
"""

from __future__ import annotations

import random
from collections import Counter

import numpy as np

import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from probe_fsmf_predecessor_miniature_census import (  # noqa: E402
    build_domain, padd, pmul, pscale, vanishing)

P, N, K = 193, 64, 16


def main():
    xs = build_domain(P, N)
    xs_np = np.array(xs, dtype=np.int64)
    rng = random.Random(31337)
    hist = Counter()
    trials = 200000
    worst = 0
    for _ in range(trials):
        idx = rng.sample(range(N), 28)
        S = [xs[i] for i in idx[:14]]
        T = [xs[i] for i in idx[14:]]
        s = rng.randrange(P)
        u = rng.randrange(P)
        lam = rng.randrange(1, P)
        A12 = pmul(vanishing(S, P), [(-s) % P, 1], P)
        A23 = pscale(lam, pmul(vanishing(T, P), [(-u) % P, 1], P), P)
        A13 = padd(A12, A23, P)
        vals = np.zeros(N, dtype=np.int64)
        acc = np.ones(N, dtype=np.int64)
        for c in A13:
            vals = (vals + c * acc) % P
            acc = acc * xs_np % P
        z = int((vals == 0).sum())
        hist[z] += 1
        worst = max(worst, z)
    print(f"trials = {trials}")
    print("histogram |zeros(A12+A23) cap domain|:",
          dict(sorted(hist.items())))
    print(f"max observed = {worst} (need >= 13 for a third large core; "
          f"fibre ansatz achieves 14 by construction)")


if __name__ == "__main__":
    main()
