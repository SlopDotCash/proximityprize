#!/usr/bin/env python3
"""
G298 exact probe: the depth-1 CORE covariance is a subgroup additive-energy threshold, and its
sign is NOT fixed by thinness.

Reproduces, with pure integer arithmetic (no floats in the load-bearing checks):

  1. The exact closed form  A_1 = p * T3(G) - n^3, where
       W_G(x) = #{(y,z) in G^2 : 2y - z = x},
       T3(G)  = sum_{x in G} W_G(x) = #{(y,z) in G^2 : 2y - z in G}
              = #{(y,z,w) in G^3 : 2y = z + w}   (3-term APs with midpoint in G),
       A_1    = centeredCov(p, W_G, 1_G) = p * sum_x W_G(x) 1_G(x) - (sum W_G)(sum 1_G),
     verified on every sponsor cell (n in {8,16}, p = 1 mod n, p < 500).

  2. Sign-indeterminacy: over the same subgroup order n, sign(A_1) takes BOTH values. The Lean
     witnesses are the identical-T3 pair:
        n=8, p=17:  T3=24, A_1 = 17*24 - 512 = -104 (< 0)
        n=8, p=41:  T3=24, A_1 = 41*24 - 512 = +472 (> 0)

Hard SystemExit(1) on any violation.
"""
import itertools
import sys


def subgroup(p, n):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        o = 1
        xx = cand % p
        while xx != 1:
            xx = (xx * cand) % p
            o += 1
            if o > p:
                break
        if o == p - 1:
            g = cand
            break
    assert g is not None, (p, n)
    h = pow(g, (p - 1) // n, p)
    G = set()
    v = 1
    for _ in range(n):
        G.add(v)
        v = (v * h) % p
    assert len(G) == n
    return sorted(G)


def W_G(G, p):
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    return W


def T3(G, p):
    Gset = set(G)
    c = 0
    for y in G:
        for z in G:
            if (2 * y - z) % p in Gset:
                c += 1
    return c


def A1(G, p):
    """Depth-1 centered covariance: R_1 = 1_G, so
    A_1 = p * sum_{x in G} W(x) - (sum W)(|G|)."""
    W = W_G(G, p)
    sW = sum(W)
    n = len(G)
    dot = sum(W[x] for x in G)
    return p * dot - sW * n


def sgn(v):
    return 0 if v == 0 else (1 if v > 0 else -1)


def main():
    fails = 0

    # 1. exact closed form A_1 = p*T3 - n^3 on all sponsor cells
    for n in (8, 16):
        primes = [p for p in range(n + 1, 500)
                  if all(p % d for d in range(2, int(p ** 0.5) + 1)) and (p - 1) % n == 0]
        signs = set()
        for p in primes:
            G = subgroup(p, n)
            T = T3(G, p)
            a1 = A1(G, p)
            pred = p * T - n ** 3
            if a1 != pred:
                print(f"FAIL closed-form n={n} p={p}: A1={a1} pred={pred}")
                fails += 1
            # also T3 == sum_{x in G} W(x)
            W = W_G(G, p)
            if T != sum(W[x] for x in G):
                print(f"FAIL T3 identity n={n} p={p}")
                fails += 1
            signs.add(sgn(a1))
        both = {1, -1} <= signs
        print(f"n={n}: {len(primes)} sponsor primes, signs={sorted(signs)}, both_signs={both}")
        if not both:
            print(f"FAIL sign-indeterminacy at n={n}: only saw {signs}")
            fails += 1

    # 2. the exact Lean witness pair (identical T3, opposite sign)
    checks = [(17, 8, 24, -104), (41, 8, 24, 472)]
    for p, n, expT, expA in checks:
        G = subgroup(p, n)
        T = T3(G, p)
        a1 = A1(G, p)
        if T != expT or a1 != expA:
            print(f"FAIL witness p={p} n={n}: T3={T}(exp {expT}) A1={a1}(exp {expA})")
            fails += 1
        else:
            print(f"witness p={p} n={n}: T3={T}, A1={a1}  OK")

    # sharpest point: same T3, threshold n^3/T3 = 512/24 between 17 and 41
    thr = 8 ** 3 / 24
    print(f"threshold n^3/T3 = 512/24 = {thr:.4f}; 17 < {thr:.2f} < 41 -> sign flip")
    if not (17 < thr < 41):
        print("FAIL threshold placement")
        fails += 1

    if fails:
        print(f"\nG298 PROBE FAILED with {fails} violation(s)")
        sys.exit(1)
    print("\nG298 PROBE PASS: A_1 = p*T3 - n^3 exact on all cells; sign takes both values; "
          "witnesses (17,8) and (41,8) share T3=24 with opposite sign.")


if __name__ == "__main__":
    main()
