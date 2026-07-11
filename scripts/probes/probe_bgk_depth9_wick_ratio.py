#!/usr/bin/env python3
"""Probe: depth-9 Wick ratio E_9(mu_n)/(17!! * n^9) for small smooth subgroups.

Context (#466 BGK depth-9 threshold, _BGKDepthNineThreshold.lean): the lane's open input is
E_9(mu_n) <= 17!! * n^9 at n = 2^30, p ~ 2^158.  Memory: exact Wick is FALSE at depth 3 for
n = 32 — so check whether the depth-9 constant 17!! = 34459425 already fails at small scale,
and how much of the weld's 2^5 slack the small-scale excess would eat.

E_9 = (1/p) * sum_b |eta_b|^18, eta_b = sum_{y in mu_n} exp(2 pi i b y / p).
Computed exactly-ish in float via the additive-character transform (vector over b in F_p).
"""
import cmath
import math
import sys

DF17 = 34459425  # 17!!


def subgroup(p: int, n: int):
    # find generator of F_p^*
    def is_gen(g):
        seen = set()
        x = 1
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        return len(seen) == p - 1
    g = 2
    while not is_gen(g):
        g += 1
    h = pow(g, (p - 1) // n, p)
    G = set()
    x = 1
    for _ in range(n):
        G.add(x)
        x = x * h % p
    assert len(G) == n
    return sorted(G)


def depth_energy_ratio(p: int, n: int, r: int = 9):
    G = subgroup(p, n)
    tot = 0.0
    w = 2j * math.pi / p
    for b in range(1, p):
        eta = sum(cmath.exp(w * ((b * y) % p)) for y in G)
        tot += abs(eta) ** (2 * r)
    # off-zero sum; E_r = (offzero + n^{2r}) / p
    Er = (tot + float(n) ** (2 * r)) / p
    wick = DF17 * float(n) ** r
    return Er, wick, Er / wick


def main():
    cases = []
    # smooth n | p-1, tiny scales (p up to ~4000 keeps runtime sane)
    for (p, n) in [(97, 8), (193, 16), (257, 16), (641, 16), (769, 16),
                   (257, 32)] :
        if (p - 1) % n != 0:
            continue
        Er, wick, ratio = depth_energy_ratio(p, n)
        cases.append((p, n, Er, wick, ratio))
        print(f"p={p:5d} n={n:3d}  E9={Er:.4e}  17!!*n^9={wick:.4e}  ratio={ratio:.4f}")
    worst = max(c[4] for c in cases)
    print(f"\nworst ratio = {worst:.4f}  (weld slack allows ratio <= 32)")
    if worst > 32:
        print("!! depth-9 Wick + slack VIOLATED at small scale — hypothesis shape suspect")
        sys.exit(1)
    elif worst > 1:
        print("exact 17!! constant exceeded at small scale; within the 2^5 weld slack")
    else:
        print("exact 17!! constant holds on all probed instances")


if __name__ == "__main__":
    main()
