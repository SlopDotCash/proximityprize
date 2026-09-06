#!/usr/bin/env python3
"""Sample the domain-zero count of a sum of two degree-15 polynomials.

Over the 64-point multiplicative domain in F_193, sample disjoint 14-subsets
S and T, independent s,u in F_193, and nonzero lambda. Construct
A12 = Z_S(X)(X-s), A23 = lambda Z_T(X)(X-u), and count domain zeros of
A12 + A23. The 200,000 trials use random.Random(31337).

This tests the specified sampling distribution, not all triples or the
geometric realizability of large joint cores. The historical threshold and
fibre comparison in the output are context, not conclusions of this probe.
For each fixed domain point the zero probability is 1/193, so the expected
number of domain zeros per trial is 64/193; degree times domain density is
not the expected root count of a random polynomial.

Pure Python plus NumPy. See the retained-evidence audit for the calculation
and the limits of the archived histogram.
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
