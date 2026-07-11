#!/usr/bin/env python3
"""Probe: integrality + wraparound purity of the zero-sum counts f_r(0) (#466 DQR-4).

Theory (session 2026-07-11): the solution set {y in G^r : sum y = 0} carries a free
G x Z/r action (dilation x cyclic shift; free because u^r = 1 and u in mu_{2^k} force
u = 1 for odd r, and constant tuples need r*y0 = 0, impossible for y0 != 0, p !| r).
Prediction: n*r | f_r(0) for odd prime r. Also Lam-Leung for 2-power n: char-0
vanishing sums of odd length do not exist, so odd-r f_r(0) is PURE WRAPAROUND.

Verified (see transcript 2026-07-11): n*r | f_r(0) at all probed (p,n,r); odd-r counts
vanish identically where wraparound cannot reach (p=12289, n=32, r=3,5).
These divisibilities are exact integrality constraints on the twist-average closed form
P_k*P_j (twistAverage_factorizes) — target Lean brick: free-action divisibility via
MulAction.card_modEq_card_fixedPoints for the shift, plus dilation orbits.
"""
import sys; sys.path.insert(0, __file__.rsplit('/',1)[0])
from probe_bgk_depth9_wick_ratio import subgroup

def frep0(p, n, r):
    G = subgroup(p, n)
    f = [0]*p; f[0] = 1
    for _ in range(r):
        g = [0]*p
        for d in range(p):
            if f[d]:
                for y in G: g[(d+y) % p] += f[d]
        f = g
    return f[0]

if __name__ == "__main__":
    ok = True
    for (p, n) in [(97,8),(193,16),(257,16),(641,16),(769,16),(257,32),(12289,32)]:
        for r in (3,5,7):
            v = frep0(p, n, r)
            div = v % (n*r) == 0
            ok &= div
            print(f"p={p:6d} n={n:2d} r={r}: f_r(0)={v:>12d} n*r|f:{div}")
    print("ALL n*r DIVISIBILITIES HOLD" if ok else "!! DIVISIBILITY VIOLATED")
    sys.exit(0 if ok else 1)
