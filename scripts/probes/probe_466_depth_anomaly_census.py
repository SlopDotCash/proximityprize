#!/usr/bin/env python3
"""Per-cancellation-depth anomaly census for multiplicative subgroups (#466/#505).

Measures the G96/G101 objects exactly, at accessible scale:

  depthFiber(G, r, s)      = #{(v, w) in G^r x G^r : sum v = sum w,
                               |bag(v) - bag(v) /\\ bag(w)| = s}
  allPairsDepthFiber(G,r,s) = same without the equal-sum condition
  actualDepthAnomaly(s)     = q * depthFiber_s - allPairsDepthFiber_s   (integer, signed)

Questions answered per (p, n, r):
  1. Sign pattern of the per-depth anomalies (tests the odd/even-sign consumer G105
     and the guarded depth-two positivity G108/G109 on REAL subgroups).
  2. Where the positive anomaly mass sits (which depths carry the DC-subtracted moment).
  3. Whether each positive anomaly fits a per-depth share of the Wick budget
     q * (2r-1)!! * n^r  — i.e. whether the G96 centered per-depth route is
     empirically localizable, or cross-depth cancellation (G100) is mandatory.

Method: enumerate multisets (combinations_with_replacement) of size r from G, group
by sum; pair multisets within a sum class; depth = r - |common multiset|; each
multiset pair contributes perm(M) * perm(N) ordered pairs. Exact integer arithmetic.

Usage: python3 probe_466_depth_anomaly_census.py [--nmax 16] [--rmax 6]
"""

import argparse
import sys
from collections import Counter, defaultdict
from itertools import combinations_with_replacement
from math import factorial


def double_factorial_odd(r: int) -> int:
    out = 1
    for k in range(2 * r - 1, 0, -2):
        out *= k
    return out


def perm_count(ms: tuple) -> int:
    c = Counter(ms)
    out = factorial(len(ms))
    for v in c.values():
        out //= factorial(v)
    return out


def subgroup(p: int, n: int):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        seen, x, ok = set(), 1, True
        for _ in range(p - 1):
            x = x * cand % p
            if x in seen:
                ok = False
                break
            seen.add(x)
        if ok and len(seen) == p - 1:
            g = cand
            break
    assert g is not None
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x)
        x = x * h % p
    assert len(set(H)) == n
    return sorted(H)


def depth_census(p: int, H: list, r: int):
    n = len(H)
    by_sum = defaultdict(list)
    for ms in combinations_with_replacement(H, r):
        by_sum[sum(ms) % p].append(ms)

    eq_fiber = [0] * (r + 1)     # depthFiber (equal-sum)
    perms = {}

    def pc(ms):
        if ms not in perms:
            perms[ms] = perm_count(ms)
        return perms[ms]

    def depth(a, b):
        ca, cb = Counter(a), Counter(b)
        common = sum((ca & cb).values())
        return r - common

    for _, group in by_sum.items():
        for i, a in enumerate(group):
            pa = pc(a)
            for b in group[i:]:
                d = depth(a, b)
                w = pa * pc(b)
                eq_fiber[d] += w if a == b else 2 * w

    # population fibers by exchangeability DP: all group elements are interchangeable
    # without the sum condition. State: (used_v, used_w, common); transition: element i
    # gets counts (a, b) with weight 1/(a! b!); scale by (r!)^2 at the end.
    from fractions import Fraction
    dp = {(0, 0, 0): Fraction(1)}
    for _ in range(n):
        ndp = defaultdict(Fraction)
        for (ua, ub, cm), wgt in dp.items():
            for a in range(r - ua + 1):
                for b in range(r - ub + 1):
                    ndp[(ua + a, ub + b, cm + min(a, b))] += \
                        wgt / (factorial(a) * factorial(b))
        dp = ndp
    pop_fiber = [0] * (r + 1)
    fr2 = factorial(r) ** 2
    for (ua, ub, cm), wgt in dp.items():
        if ua == r and ub == r:
            val = wgt * fr2
            assert val.denominator == 1
            pop_fiber[r - cm] += int(val)

    assert sum(pop_fiber) == n ** (2 * r), "population check failed"
    assert sum(eq_fiber[s] for s in range(r + 1)) <= sum(pop_fiber)
    return eq_fiber, pop_fiber


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=16)
    ap.add_argument("--rmax", type=int, default=6)
    ap.add_argument("--random", type=int, default=0,
                    help="also test K random n-subsets of ZMod p per cell (control)")
    args = ap.parse_args()

    cases = []
    for n in (4, 8, 16, 32):
        if n > args.nmax:
            continue
        # two primes per n: smallest and one mid-range with p ≡ 1 (mod n), p > n^2
        found = []
        cand = n * n + 1
        while len(found) < 2 and cand < 10 * n * n + 1000:
            if (cand - 1) % n == 0 and all(cand % q for q in range(2, int(cand ** 0.5) + 1)):
                found.append(cand)
                cand += n * n  # skip ahead for spread
            cand += 1
        for p in found:
            cases.append((p, n))

    import random as rnd
    rnd.seed(466)
    overall_violations = 0

    def report(tag, p, n, r, H):
        nonlocal overall_violations
        eq, pop = depth_census(p, H, r)
        wick = double_factorial_odd(r) * n ** r
        anomalies = [p * eq[s] - pop[s] for s in range(r + 1)]
        total = sum(anomalies)
        signs = "".join("+" if a > 0 else ("-" if a < 0 else "0") for a in anomalies)
        per_depth_ok = all(a <= p * wick for a in anomalies)
        dc_ok = total <= p * wick
        if not dc_ok:
            overall_violations += 1
        print(f"{tag} p={p:6d} n={n:3d} r={r} signs[s=0..r]={signs} "
              f"total/(q*Wick)={total / (p * wick):+.6f} "
              f"max_pos/(q*Wick)={max(anomalies) / (p * wick):+.6f} "
              f"perdepth_ok={per_depth_ok} DC_ok={dc_ok}")
        sys.stdout.flush()

    from math import comb
    for p, n in cases:
        H = subgroup(p, n)
        for r in range(2, args.rmax + 1):
            if comb(n + r - 1, r) > 40000:
                continue
            report("SUBGRP", p, n, r, H)
            for _ in range(args.random):
                S = sorted(rnd.sample(range(1, p), n))
                report("RANDOM", p, n, r, S)

    print(f"\nDC violations: {overall_violations} (expected 0 — DCEnergyBound "
          f"measured true at accessible scale)")


if __name__ == "__main__":
    main()
