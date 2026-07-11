#!/usr/bin/env python3
"""SYZ7 strip scan: is any radius in the conceptual gap (Johnson, 1/3) killable
at production rate 1/2?

Context (issues #466/#507).  The SYZ degenerate-subset channel (SYZ1..SYZ6)
gives unconditional production rate-1/2 ceilings approaching the channel infimum
`(1-rho)/(2-rho) = 1/3` at `rho = 1/2`, but PROVABLY cannot cross it: each
degenerate subset of agreement size `t` costs `2(t-k)` syndrome rank out of the
`2(n-k)` budget, so `D <= (n-k)/(t-k)` subsets carry at most `D*(n-t)` bad
scalars, and `D*(n-t) > (budget ~ n)` forces `delta = (n-t)/n > (1-rho)/(2-rho)`.
The open strip `[Johnson = 1 - sqrt(rho) ~ 0.2929, 1/3]` lies strictly BELOW that
infimum -- the channel starves there.

This probe does NOT try to prove the strip unreachable (that is a theorem about a
specific channel; a genuinely different construction is not ruled out).  It
empirically maps the certified max-bad-count curve vs radius across and around the
strip at small faithful cells (n = 32, 64, rate 1/2), in the LARGE-field regime
(p >> C(n,t)/n so generic/random stacks are clean, matching the prize regime), by
running every degenerate-channel variant we can construct and FULLY verifying each
candidate scalar against the literal `mcaEvent` (agreement set + NOT pairJoint,
two independent interpolation paths).  Families scanned per threshold t:

  * A_D : D shared degenerate subsets of size t, D = 1..Dmax+1 (the SYZ channel);
  * NEAR: near-degenerate subsets (size t-1, padded by extra agreement) -- tests
    the SYZ7 question 1(b) "witness within distance 1 of the code" loophole;
  * MIX : mixed-threshold subsets (sizes t, t+1, t-1) -- tests SYZ7 question 1(a)
    "smaller-t_j witnesses piggyback" loophole;
  * RAND: random low-rank syndrome-pair stacks (non-channel control).

Budget analogue = n (production: eps* * q ~ n).  A radius delta = (n-t)/n is
"killed" iff some stack certifies > n bad scalars at threshold t.

Deterministic, exact modular arithmetic.  Reuses the fully-verified harness of
`probe_syzygy_configuration_bad_counts.py`.
Run:  python3 scripts/probes/probe_syz7_strip_scan.py
"""

import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_syzygy_configuration_bad_counts import (  # noqa: E402
    Domain, next_prime_1_mod, witness_rows, solve_stack,
    analyze_stack, agrees_with_code_on, batch_inverse,
)

MASTER_SEED = "syz7-strip"
JOHNSON = 1 - math.sqrt(0.5)   # ~0.29289
THIRD = 1.0 / 3.0              # ~0.33333


def degenerate_rows_general(dom, S):
    """(t-k) x 2 rows on F^{2n} forcing BOTH u0|S and u1|S to be restrictions of
    degree<k codewords, valid for ANY t = |S| >= k (the imported harness's
    `degenerate_rows` is hardcoded to t-k = 2).  For each of the last (t-k) nodes
    s of S, impose  u[s] = sum_j L_j(x_s) * u[S[j]]  (Lagrange interp through the
    first k nodes), i.e. one parity row per extra node, per u-block."""
    n, p, k = dom.n, dom.p, dom.k
    S = list(S)
    nodes = S[:k]
    xs = dom.xs
    xn = [xs[i] for i in nodes]
    # barycentric denominators for the k interpolation nodes
    den = []
    for j, xj in enumerate(xn):
        acc = 1
        for l, xl in enumerate(xn):
            if l != j:
                acc = acc * (xj - xl) % p
        den.append(acc)
    invden = batch_inverse(den, p)
    rows = []
    for s in S[k:]:
        x = xs[s]
        # numerator prod (x - xl)
        Z = 1
        for xl in xn:
            Z = Z * (x - xl) % p
        # L_j(x) = Z / ((x - x_j) * den_j)
        Ls = []
        diffs = [(x - xl) % p for xl in xn]
        invdiffs = batch_inverse(diffs, p)
        for j in range(k):
            Ls.append(Z * invdiffs[j] % p * invden[j] % p)
        for blk in (0, n):
            vec = [0] * (2 * n)
            vec[blk + s] = 1
            for j, node in enumerate(nodes):
                vec[blk + node] = (-Ls[j]) % p
            rows.append(vec)
    return rows


def build_degenerate_stack(dom, subsets, rng, tries=6):
    """Plant a non-codeword-pair stack forced degenerate on every S in subsets."""
    rows = []
    for S in subsets:
        rows.extend(degenerate_rows_general(dom, S))
    return solve_stack(dom, rows, rng, tries=40)


def scan_threshold(dom, rng, families):
    """Return dict family -> max certified bad-count over attempts at this t."""
    n, k, t = dom.n, dom.k, dom.t
    m = t - k
    dmax = max(1, (n - k) // m - 1)
    best = {f: 0 for f in families}

    def try_stack(fam, u0, u1, subsets):
        if u0 is None:
            return
        res = analyze_stack(dom, fam, u0, u1, subsets, rng)
        if res["certified"] > best[fam]:
            best[fam] = res["certified"]

    # Family A: D shared degenerate subsets of size t
    if "A" in families:
        for D in sorted({1, 2, dmax, dmax + 1}):
            if D < 1:
                continue
            for _ in range(3):
                subs = [tuple(sorted(rng.sample(range(n), t))) for _ in range(D)]
                u0, u1, _ = build_degenerate_stack(dom, subs, rng)
                try_stack("A", u0, u1, subs)

    # Family NEAR: subsets of size t-1 (near-degenerate: line within distance 1
    # of code contributes only if the extra agreement pads back to size t)
    if "NEAR" in families and t - 1 > k:
        tt = t - 1
        for D in sorted({1, 2, dmax, dmax + 1}):
            if D < 1:
                continue
            for _ in range(3):
                subs = [tuple(sorted(rng.sample(range(n), tt))) for _ in range(D)]
                rows = []
                for S in subs:
                    rows.extend(degenerate_rows_general(dom, S))
                u0, u1, _ = solve_stack(dom, rows, rng, tries=40)
                # analyze at the ACTUAL threshold t (radius delta=(n-t)/n)
                try_stack("NEAR", u0, u1, subs)

    # Family MIX: mixed-threshold subsets (sizes t-1, t, t+1)
    if "MIX" in families:
        sizes = [s for s in (t - 1, t, t + 1) if k < s <= n]
        for _ in range(6):
            D = min(dmax + 1, 4)
            subs = []
            for i in range(D):
                sz = sizes[i % len(sizes)]
                subs.append(tuple(sorted(rng.sample(range(n), sz))))
            rows = []
            for S in subs:
                rows.extend(degenerate_rows_general(dom, S))
            u0, u1, _ = solve_stack(dom, rows, rng, tries=40)
            try_stack("MIX", u0, u1, subs)

    # Family RAND: random low-rank syndrome-pair stacks (non-channel control)
    if "RAND" in families:
        for _ in range(8):
            # a handful of random (S,gamma) witness rows, well under full rank
            plan = []
            for _ in range(min(dmax, 3)):
                plan.append((rng.randrange(1, dom.p),
                             tuple(sorted(rng.sample(range(n), t)))))
            rows = []
            for gam, S in plan:
                rows.extend(witness_rows(dom, gam, S))
            u0, u1, _ = solve_stack(dom, rows, rng, tries=40)
            subs = [S for _, S in plan]
            try_stack("RAND", u0, u1, subs)

    return best, dmax


def strip_band(n, k):
    """t-thresholds spanning [below Johnson .. above 1/3] for calibration.
    Radius delta = (n-t)/n; strip is Johnson < delta < 1/3."""
    out = []
    for t in range(k + 2, n):
        delta = (n - t) / n
        if 0.24 <= delta <= 0.40:
            out.append((t, delta))
    return out


def run():
    print("SYZ7 strip scan: certified max-bad-count vs radius across (Johnson, 1/3)")
    print(f"rate 1/2; Johnson = 1 - sqrt(1/2) = {JOHNSON:.5f}; "
          f"channel infimum 1/3 = {THIRD:.5f}; budget analogue = n")
    print("channel yield bound: D*(n-t) with D <= (n-k)/(t-k)")
    families = ["A", "NEAR", "MIX", "RAND"]
    all_rows = []
    for n, k, tag, tgt in ((32, 16, "2^30", 1 << 30), (64, 32, "2^60", 1 << 60)):
        p = next_prime_1_mod(n, tgt)
        print(f"\n==== CELL n={n} k={k} p={p} (~2^{math.log2(p):.1f}, {tag}), "
              f"budget={n} ====")
        band = strip_band(n, k)
        print(f"  {'t':>3} {'delta':>7} {'zone':<10} {'chanBound':>9} "
              f"{'A':>4} {'NEAR':>4} {'MIX':>4} {'RAND':>4} {'maxBad':>6} verdict")
        for t, delta in band:
            dom = Domain(n, k, t, p)
            rng = random.Random(f"{MASTER_SEED}-{n}-{t}")
            best, dmax = scan_threshold(dom, rng, families)
            chan_bound = dmax * (n - t)
            maxbad = max(best.values())
            if delta < JOHNSON:
                zone = "below-J"
            elif delta < THIRD:
                zone = "STRIP"
            elif delta < THIRD + 1e-9:
                zone = "=1/3"
            else:
                zone = "above-1/3"
            killed = maxbad > n
            verdict = "KILLED" if killed else "survives"
            print(f"  {t:>3} {delta:>7.4f} {zone:<10} {chan_bound:>9} "
                  f"{best['A']:>4} {best['NEAR']:>4} {best['MIX']:>4} "
                  f"{best['RAND']:>4} {maxbad:>6} {verdict}")
            all_rows.append((n, t, delta, zone, maxbad, killed))

    print("\n\nVERDICT (SYZ7 question 1e):")
    strip_killed = [r for r in all_rows if r[3] == "STRIP" and r[5]]
    if strip_killed:
        print("  SOME STRIP RADIUS KILLED empirically:")
        for r in strip_killed:
            print(f"    n={r[0]} t={r[1]} delta={r[2]:.4f} maxBad={r[4]} > n")
    else:
        print("  NO radius in the strip (Johnson, 1/3) killed by any scanned family.")
        print("  Consistent with the channel infimum 1/3 (rank-budget theorem):")
        print("  the degenerate channel and its near-/mixed-threshold variants all")
        print("  starve below 1/3.  This is search evidence, NOT a proof that no")
        print("  construction can reach the strip (CONJECTURE: strip unreachable).")
    above = [r for r in all_rows if r[3] == "above-1/3" and r[5]]
    print(f"\n  Calibration: {len(above)} radii ABOVE 1/3 killed (channel active there)"
          f" -- confirms the harness certifies over-budget stacks when they exist.")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run()
