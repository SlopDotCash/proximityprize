#!/usr/bin/env python3
"""#466 thread ll:low-profile-fiber (prefix w9): the ROOT-PENCIL SATURATION probe.

CLAIM UNDER TEST (fabricate-then-refute, aimed at the weld's `hsafe`/`hlowFiber`
production obligations): on zero-direction-SAFE, large-zero (z >= a) lines, the
bad-scalar count and the low-profile (t < k) strata D(t) admit sub-q bounds.

CANDIDATE COUNTEREXAMPLE (the "root pencil"): pick a codeword e of degree <= k-1
whose root set R (inside dom) sits in the direction's zero set, put

    u1 = e on S (moving support, S disjoint from R, e != 0 on S), u1 = 0 off S,
    u0 = 1 on a small set W inside Z minus R, u0 = 0 elsewhere,

with |S| + |R| >= a, z = n - |S| >= a, n - |S| - |W| < a, (k-1) + |W| < a.
(No escape sequences below; module docstring kept ASCII-clean.)
Then for EVERY scalar gamma the codeword gamma*e agrees with the line word
u0 + gamma*u1 on all of S (u0 = 0 there) and all of R (both sides 0):
agreement >= |S|+|R| >= a, so lineBadScalars = the whole field, while the line
stays zero-direction-safe by pure zero-counting.  The saturating stratum is
t = |R| <= k-1 < k: LOW-PROFILE.

This probe verifies every claim EXHAUSTIVELY over all q^k codewords at
n=16, k=4, a=9 (the rate-quarter shape of the sibling program) over GF(17)
and GF(23), for both mid-band supports s in {6,7}; it also computes the true
mcaEvent count on the same lines.  Measured: the mcaEvent count is exactly
1 + |W| (the special scalars gamma = 0 and the W-ratio scalars, whose enlarged
witness sets escape the joint pair (0, e)); the generic q - 1 - |W| pencil
scalars are all joint-pair-explained on their witnesses.  The gap q vs 1+|W|
exhibits the exact lossy step mcaEvent_filter_subset_lineBadScalars.

Exit 0 iff all assertions hold.
"""

import itertools
import sys


def run_config(q, n, k, a, S, R, W, root_pts):
    """Build the configuration and exhaustively verify.  Returns dict of results."""
    dom = list(range(n))  # dom i = i in GF(q), injective for n <= q
    assert n <= q
    S, R, W = set(S), set(R), set(W)
    assert not (S & R) and not (S & W) and not (R & W)
    s, r, w = len(S), len(R), len(W)
    Z = set(dom) - S  # zero set of u1 (indices)
    V = Z - R - W

    # e = prod_{rho in root_pts} (X - rho); root_pts = dom points of R
    def eval_e(x):
        v = 1
        for rho in root_pts:
            v = (v * (x - rho)) % q
        return v

    e = [eval_e(i) for i in dom]
    assert all(e[i] == 0 for i in R), "e must vanish on R"
    assert all(e[i] != 0 for i in S), "e must be nonzero on S"
    assert all(e[i] != 0 for i in V | W), "e roots must be exactly R inside dom"

    u1 = [e[i] if i in S else 0 for i in dom]
    u0 = [1 if i in W else 0 for i in dom]

    # sanity: parameter regime
    assert a <= s + r, "badness threshold"
    assert n - s >= a, "large-zero (not support-eligible)"
    assert a < k + s, "mid band (a < k + support)"
    assert n - s - w < a and (k - 1) + w < a, "safety counting conditions"

    # enumerate all codewords (evaluations of deg<k polys)
    def poly_eval(coeffs, x):
        v = 0
        for c in reversed(coeffs):
            v = (v * x + c) % q
        return v

    codewords = []
    for coeffs in itertools.product(range(q), repeat=k):
        codewords.append(tuple(poly_eval(coeffs, x) for x in dom))
    assert len(set(codewords)) == q ** k

    # 1. SAFETY: max zero-agreement with u0 over ALL codewords < a
    max_zero_agree = 0
    for c in codewords:
        za = sum(1 for i in Z if c[i] == u0[i])
        max_zero_agree = max(max_zero_agree, za)
    safe = max_zero_agree < a

    # 2. BAD SCALARS + full stratum profile, exhaustively
    bad = set()
    appearing = {}  # codeword -> exact zero-agreement count t
    for gamma in range(q):
        wg = [(u0[i] + gamma * u1[i]) % q for i in dom]
        for c in codewords:
            agree = sum(1 for i in dom if c[i] == wg[i])
            if agree >= a:
                bad.add(gamma)
                t = sum(1 for i in Z if c[i] == u0[i])
                appearing[c] = t
    D = {}
    for c, t in appearing.items():
        D[t] = D.get(t, 0) + 1

    # 3. the pencil is inside the count: gamma*e appears for every gamma
    for gamma in range(q):
        ce = tuple((gamma * e[i]) % q for i in dom)
        wg = [(u0[i] + gamma * u1[i]) % q for i in dom]
        agree = sum(1 for i in dom if ce[i] == wg[i])
        assert agree >= a, (gamma, agree)

    # 4. mcaEvent count on this line (delta with (1-delta)*n = a):
    #    mcaEvent(gamma) iff exists codeword c with A = agree(c, w_gamma),
    #    |A| >= a and NO joint pair (v0,v1) with v0=u0, v1=u1 on A.
    #    (witness maximality: pairJointAgreesOn is antitone in S)
    cw_set = set(codewords)

    def jointly_explained(A):
        # exists v0 codeword: v0 = u0 on A;  exists v1 codeword: v1 = u1 on A
        # (independent searches; interpolate from any k points of A + check)
        def explainable(target):
            pts = sorted(A)
            # brute: check all codewords (q^k small)
            for c in codewords:
                if all(c[i] == target[i] for i in pts):
                    return True
            return False

        return explainable(u0) and explainable(u1)

    mca_count = 0
    for gamma in range(q):
        wg = [(u0[i] + gamma * u1[i]) % q for i in dom]
        fired = False
        for c in codewords:
            A = frozenset(i for i in dom if c[i] == wg[i])
            if len(A) >= a and not jointly_explained(A):
                fired = True
                break
        if fired:
            mca_count += 1

    return dict(q=q, s=s, r=r, w=w, z=n - s, safe=safe,
                max_zero_agree=max_zero_agree, n_bad=len(bad),
                strata=dict(sorted(D.items())), mca_count=mca_count)


def main():
    n, k, a = 16, 4, 9
    all_ok = True
    for q in (17, 23):
        # config A: mid-band support s=6, roots r=3=k-1, stratum t=3<k saturates
        resA = run_config(q, n, k, a,
                          S=range(0, 6), R={13, 14, 15}, W={6, 7},
                          root_pts=[13, 14, 15])
        # config B: mid-band support s=7 (z=a exactly), roots r=2, stratum t=2<k
        resB = run_config(q, n, k, a,
                          S=range(0, 7), R={14, 15}, W={7},
                          root_pts=[14, 15])
        for name, res in (("A(s=6,r=3)", resA), ("B(s=7,r=2)", resB)):
            print(f"q={q} config {name}: {res}")
            ok = (res["safe"]
                  and res["n_bad"] == q                      # FULL FIELD bad
                  and res["strata"].get(res["r"], 0) >= q - 1 - res["w"]
                  and res["mca_count"] <= 1 + res["w"])      # prize object stays O(1)
            print(f"  -> safe={res['safe']} badScalars={res['n_bad']}/{q} "
                  f"D({res['r']})={res['strata'].get(res['r'], 0)} "
                  f"mcaEvents={res['mca_count']}  {'OK' if ok else 'FAIL'}")
            all_ok = all_ok and ok

    print()
    if all_ok:
        print("VERDICT: root-pencil saturation CONFIRMED -- zero-direction-safe,"
              " large-zero, mid-band lines with lineBadScalars = FULL FIELD and the"
              " saturating stratum at t = r < k (low-profile).  The weld obligations"
              " LargeZeroSafeLineBadScalarsBudgeted / MidBandSafeLineBadScalarsBudgeted /"
              " hlowFiber(M t << q^(k-t)) are REFUTED below B = q; the mcaEvent count"
              " on the same lines is only 1+|W| (joint pair (0,e) explains all generic"
              " pencil scalars) -- the lossy step is exactly"
              " mcaEvent_filter_subset_lineBadScalars.")
        return 0
    print("VERDICT: FAILED -- construction does not behave as claimed")
    return 1


if __name__ == "__main__":
    sys.exit(main())
