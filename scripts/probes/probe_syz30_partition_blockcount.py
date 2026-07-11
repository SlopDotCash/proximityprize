#!/usr/bin/env python3
"""
SYZ30 lemma 3: which block-count achieves the D>=4 over-budget min envelope, and the per-m slack.

Confirms the SYZ30 case split for the all-partition minimization
    envelope(P) = sum over blocks B of (|union_{i in B} C_i| - k),   min >= n-k ?
over random band full covers (band 2n/3 < s < 3n/4, rate 1/2, k=n/2):

  * argmin block-count is ALWAYS m=1 (whole cover), realizing n-k exactly;
  * m>=3 slack >= 2 (proved unconditionally from the band size floor: sum >= m(s-k) >= 3(s-k));
  * m=2 slack is exactly 0 (tight, never below) -- the two-block envelope equals the
    cross-intersection |U0 & U1|, and the residual is the floor |U0 & U1| >= k.

The D=3 crack is the m=2 near-duplicate-pair case where |U0 & U1| = k-1 (slack -1).
"""
import random
from probe_syz28_d3_coplanar_crack import sum_excess, band_sizes
from probe_syz29_d4_defect_formula import set_partitions, envelope_count


def analyze(n, D, trials=4000, seed=7):
    random.seed(seed)
    k = n // 2
    pts = list(range(n))
    sizes = band_sizes(n)
    ceil23 = -((-2 * n) // 3)
    if ceil23 not in sizes:
        sizes = sizes + [ceil23]
    minm_hist = {}
    slack_by_m = {}
    tested = 0
    for _ in range(trials):
        cores = []
        seen = set()
        ok = True
        for _c in range(D):
            s = random.choice(sizes)
            C = tuple(sorted(random.sample(pts, s)))
            if C in seen:
                ok = False
                break
            seen.add(C)
            cores.append(list(C))
        if not ok:
            continue
        U = set().union(*[set(c) for c in cores])
        if len(U) < n:
            continue
        if sum_excess(cores, k) < (n - k):
            continue
        tested += 1
        best = None
        bestP = None
        permin = {}
        for P in set_partitions(list(range(D))):
            v = envelope_count(cores, k, P)
            m = len(P)
            permin[m] = min(permin.get(m, 10 ** 9), v)
            if best is None or v < best:
                best = v
                bestP = P
        minm_hist[len(bestP)] = minm_hist.get(len(bestP), 0) + 1
        for m, v in permin.items():
            slack_by_m.setdefault(m, 10 ** 9)
            slack_by_m[m] = min(slack_by_m[m], v - (n - k))
    return dict(n=n, D=D, tested=tested, argmin=minm_hist, slack_by_m=slack_by_m)


if __name__ == "__main__":
    print("=== SYZ30 lemma 3: D>=4 over-budget partition block-count / slack ===")
    for n in (16, 20, 24):
        for D in (4, 5):
            r = analyze(n, D)
            print(f"n={r['n']:2d} D={r['D']} over-budget tested={r['tested']:5d}"
                  f"  argmin-block-count={r['argmin']}  min-slack-by-m={r['slack_by_m']}")
