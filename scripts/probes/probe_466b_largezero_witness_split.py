#!/usr/bin/env python3
"""probe_466b_largezero_witness_split.py  (#466 round 2, lane HLOW)

Exact brute-force verification, at small parameters, of the three counting claims of
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R2B_LargeZeroWitnessSplit.lean:

  (C1) witness split: every appearing codeword c of the line (u0, u1) at threshold a
       has zAgree(c) := #{i in Z(u1) : c i = u0 i} >= a - s,  s = #support(u1).
  (C2) stratum emptiness: zeroAgreementStratum(t) = empty for all t + s < a.
  (C3) threshold-choose cap: on ZERO-SAFE lines with k + s <= a (very-large-zero),
       #lineBadScalars <= sum_{t<a, t+s>=a} C(z,t) * (s // (a-t)).

Also records the observed max bad-count in the MID BAND (a <= z < n-a+k) on safe lines,
which the brick leaves OPEN (MidBandSafeLineBadScalarsBudgeted) -- purely informational.

Exhaustive over: all directions u1 with z >= a (large-zero branch), all offset cosets
u0 mod RS (counts are coset-invariant: c <-> c + v0 is a bijection of the code), all
gamma, all codewords.  No character sums here, so the #400 subgroup-probe trap does not
apply; the eval domain is just distinct field points.

Single-threaded, ~1-2 min.
"""

import itertools
import math
import sys
from collections import defaultdict

import numpy as np


def run_config(q, n, k, a, outf):
    dom = np.arange(n) % q  # n distinct points (n <= q)
    assert len(set(dom.tolist())) == n

    # all q^k polynomials, evaluated -> codewords (q^k x n)
    coeffs = np.array(list(itertools.product(range(q), repeat=k)))  # (q^k, k)
    vander = np.array([[pow(int(x), j, q) for j in range(k)] for x in dom])  # (n, k)
    code = (coeffs @ vander.T) % q  # (q^k, n)
    ncw = code.shape[0]

    # coset representatives of F^n / RS: fix first k coordinates of the codeword to 0
    # (RS is MDS: any k coordinates are an information set), enumerate the rest freely.
    # A transversal: words that are 0 on the first k coords in the "systematic" sense.
    # Simpler exact transversal: enumerate all words whose value on the first k domain
    # points is fixed to the word's own interpolation being zero -- equivalently take
    # all words w with w[0:k] = 0 composed with nothing: since any k coords are an
    # information set, {w : w[0]=...=w[k-1]=0} meets every coset exactly once.
    free = np.array(list(itertools.product(range(q), repeat=n - k)))
    u0s = np.zeros((free.shape[0], n), dtype=int)
    u0s[:, k:] = free  # (q^(n-k), n)

    gammas = np.arange(q)

    viol_c1 = viol_c2 = viol_c3 = 0
    checked_lines = 0
    vlz_max_ratio = 0.0  # bad/cap on very-large-zero safe lines (cap>0)
    mid_max_bad = defaultdict(int)  # z -> max bad count on safe mid-band lines
    vlz_stats = defaultdict(lambda: [0, 0])  # z -> [max bad, cap]

    # directions with z >= a zeros
    for z in range(a, n + 1):
        s = n - z
        for zero_pos in itertools.combinations(range(n), z):
            zp = list(zero_pos)
            sp = [i for i in range(n) if i not in zero_pos]
            for vals in itertools.product(range(1, q), repeat=s):
                u1 = np.zeros(n, dtype=int)
                u1[sp] = vals
                # cap (C3) for this direction
                cap = sum(
                    math.comb(z, t) * (s // (a - t))
                    for t in range(a)
                    if t + s >= a
                )
                for u0 in u0s:
                    checked_lines += 1
                    # zAgree per codeword (gamma-free)
                    zagree = (code[:, zp] == u0[zp]).sum(axis=1) if z else np.zeros(ncw, int)
                    safe = bool((zagree < a).all())
                    # agreement per (codeword, gamma)
                    # line word for gamma: u0 + gamma*u1 mod q  -> (q, n)
                    lines = (u0[None, :] + gammas[:, None] * u1[None, :]) % q
                    agree = (code[None, :, :] == lines[:, None, :]).sum(axis=2)  # (q, ncw)
                    heavy = agree >= a
                    bad = int(heavy.any(axis=1).sum())
                    appearing = heavy.any(axis=0)  # (ncw,)
                    # C1
                    if (zagree[appearing] < a - s).any():
                        viol_c1 += 1
                    # C2: strata t with t+s<a empty among appearing codewords
                    for t in range(a - s):
                        if t >= 0 and (zagree[appearing] == t).any():
                            viol_c2 += 1
                            break
                    # C3 on safe very-large-zero lines
                    if safe and k + s <= a:
                        if bad > cap:
                            viol_c3 += 1
                        vlz_stats[z][0] = max(vlz_stats[z][0], bad)
                        vlz_stats[z][1] = cap
                        if cap > 0:
                            vlz_max_ratio = max(vlz_max_ratio, bad / cap)
                    if safe and k + s > a:  # mid band
                        mid_max_bad[z] = max(mid_max_bad[z], bad)

    print(f"[q={q} n={n} k={k} a={a}] lines checked: {checked_lines}", file=outf)
    print(f"  C1 (witness split zAgree >= a-s) violations: {viol_c1}", file=outf)
    print(f"  C2 (strata t < a-s empty)        violations: {viol_c2}", file=outf)
    print(f"  C3 (threshold-choose cap, VLZ)   violations: {viol_c3}", file=outf)
    for z in sorted(vlz_stats):
        b, c = vlz_stats[z]
        print(f"  very-large-zero z={z}: max bad = {b}, cap = {c}", file=outf)
    for z in sorted(mid_max_bad):
        print(f"  mid-band (OPEN residual) z={z}: max bad on safe lines = {mid_max_bad[z]}",
              file=outf)
    ok = viol_c1 == viol_c2 == viol_c3 == 0
    print(f"  => {'PASS' if ok else 'FAIL'}", file=outf)
    return ok


def main():
    out_path = "scripts/probes/_out_466b_largezero_witness_split.txt"
    ok = True
    with open(out_path, "w") as outf:
        print("probe_466b_largezero_witness_split -- exact brute force", file=outf)
        # config 1: mid band (z=3) AND very-large-zero (z=4,5) both nonempty:
        #   k+s<=a  <=>  z >= n-a+k = 5-3+2 = 4
        ok &= run_config(q=7, n=5, k=2, a=3, outf=outf)
        # config 2: different field, same shape
        ok &= run_config(q=11, n=5, k=2, a=3, outf=outf)
        # config 3: k=3, a=4, n=6: VLZ z >= 6-4+3 = 5; mid band z=4
        ok &= run_config(q=7, n=6, k=3, a=4, outf=outf)
        print(f"OVERALL: {'PASS' if ok else 'FAIL'}", file=outf)
    with open(out_path) as f:
        sys.stdout.write(f.read())
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
