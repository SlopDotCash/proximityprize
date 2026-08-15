#!/usr/bin/env python3
# G220 opus-core FOLLOW-UP: is there a DIAGONAL-DOMINANCE decomposition of the
# physical-space signed correlation A_signed = p*C - sumW*sumR that forces sign?
#
# Prior result (oc_g220_physical_correlation_probe): A_signed = p*Sum_{chi!=1} What conj(Rhat)
# exactly (Parseval), and its SIGN is not forced (all 4 joint quadrants realized).
#
# This probe tests the SHARPER structural hope: the physical correlation
#   C = Sum_x W(x) R_r(x)
# splits as a "diagonal" support-overlap mass D plus an off-support remainder.
# Does the DC-subtracted deviation split so that ONE part has forced sign and
# dominates?  Concretely decompose relative to the uniform null mu = sumW*sumR/p:
#   A_signed = p * Sum_x ( W(x) - sumW/p ) * ( R(x) - sumR/p )    (exact, DC removed)
# We test whether the term restricted to the STRUCTURAL support
#   S = { x : W(x) > 0 }   (the 2G-G translate set, a 2-power-subgroup object)
# has a forced sign, i.e. whether concentrating R on the W-support is what sets
# the sign.  If the on-support and off-support partial sums BOTH realize both
# signs and can dominate either way, no diagonal-dominance certificate exists.
#
# All exact integers (scaled by p to clear the /p).
import sys
from itertools import combinations


def is_prime(x):
    if x < 2:
        return False
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return True


def order_of(a, p):
    o, cur = 1, a % p
    while cur != 1:
        cur = (cur * a) % p
        o += 1
    return o


def prim_root(p):
    for a in range(2, p):
        if order_of(a, p) == p - 1:
            return a
    raise RuntimeError("no primitive root")


def subgroup(p, n):
    m = (p - 1) // n
    pr = prim_root(p)
    h = pow(pr, m, p)
    G, cur = [], 1
    for _ in range(n):
        G.append(cur)
        cur = (cur * h) % p
    return sorted(set(G))


def W_profile(p, G):
    W = [0] * p
    for y in G:
        ty = (2 * y) % p
        for z in G:
            W[(ty - z) % p] += 1
    return W


def R_profile(p, G, r):
    R = [0] * p
    for A in combinations(G, r):
        R[sum(A) % p] += 1
    return R


def analyze(p, n, r):
    G = subgroup(p, n)
    W = W_profile(p, G)
    R = R_profile(p, G, r)
    sumW, sumR = sum(W), sum(R)
    # p * (W(x) - sumW/p)(R(x) - sumR/p) = p*W*R - W*sumR - R*sumW + sumW*sumR/p
    # Sum over x of the exact object (multiply by p to clear): define per-x integer
    #   t(x) = p*p*W(x)*R(x) - p*W(x)*sumR - p*R(x)*sumW + sumW*sumR
    # Sum_x t(x) = p*(p*C - sumW*sumR) = p * A_signed  (exact int). Sign(sum) = sign(A_signed).
    Wsupp = [x for x in range(p) if W[x] > 0]
    Wsupp_set = set(Wsupp)

    def tval(x):
        return p * p * W[x] * R[x] - p * W[x] * sumR - p * R[x] * sumW + sumW * sumR

    on = sum(tval(x) for x in Wsupp)                       # on W-support
    off = sum(tval(x) for x in range(p) if x not in Wsupp_set)
    total = on + off  # = p*A_signed
    return dict(p=p, n=n, r=r, m=(p - 1) // n, on=on, off=off, total=total,
                sgn_on=_s(on), sgn_off=_s(off), sgn_tot=_s(total),
                dominant=('on' if abs(on) >= abs(off) else 'off'))


def _s(v):
    return 1 if v > 0 else (-1 if v < 0 else 0)


def main():
    cells = [
        (8, 41), (8, 73), (8, 97), (8, 257), (8, 60017),
        (16, 97), (16, 257), (16, 881), (16, 977), (16, 1153),
        (32, 193), (32, 257), (32, 641), (32, 1153),
    ]
    ranks = [5, 6]
    print(f"{'p':>7} {'n':>4} {'m':>6} {'r':>2} {'sgn_on':>6} {'sgn_off':>7} "
          f"{'sgn_tot':>7} {'dominant':>8}", flush=True)
    on_signs = {5: [], 6: []}
    off_signs = {5: [], 6: []}
    dom_forces = {5: [], 6: []}  # does the dominant part's sign == total sign?
    for (n, p) in cells:
        if not is_prime(p) or (p - 1) % n != 0:
            continue
        for r in ranks:
            if r > n:
                continue
            d = analyze(p, n, r)
            on_signs[r].append(d['sgn_on'])
            off_signs[r].append(d['sgn_off'])
            dom_sign = d['sgn_on'] if d['dominant'] == 'on' else d['sgn_off']
            dom_forces[r].append(dom_sign == d['sgn_tot'])
            print(f"{d['p']:>7} {d['n']:>4} {d['m']:>6} {d['r']:>2} "
                  f"{d['sgn_on']:>6} {d['sgn_off']:>7} {d['sgn_tot']:>7} "
                  f"{d['dominant']:>8}", flush=True)
    print("\n=== DIAGONAL-DOMINANCE VERDICT ===")
    for r in ranks:
        on_p = sum(1 for v in on_signs[r] if v > 0)
        on_n = sum(1 for v in on_signs[r] if v < 0)
        off_p = sum(1 for v in off_signs[r] if v > 0)
        off_n = sum(1 for v in off_signs[r] if v < 0)
        print(f"r={r}: on-support sign {on_p}+/{on_n}-  "
              f"off-support sign {off_p}+/{off_n}-  "
              f"=> on-support {'FORCED' if (on_p == 0 or on_n == 0) else 'NOT forced'}, "
              f"off-support {'FORCED' if (off_p == 0 or off_n == 0) else 'NOT forced'}")


if __name__ == '__main__':
    main()
