#!/usr/bin/env python3
"""G87: depth-four production feasibility of the sharp envelope + pair-sum concentration.

Exact integer verification of:

  (I)   sharp-envelope depth cutoffs at (n,r)=(2^30,110) with the trivial equal-sum
        universe J_s <= n^(2s-1): depths 2,3 absorbed; depth 4 over budget by ~2^2.09
        (versus ~2^11.26 with the coarse envelope); depth 5+ far over.

  (II)  the elementary convolution chain J_4 <= (M+1)*n^6 with factor-5 pair-sum
        concentration M = n//5 closes depth four: the kernel inequality of
        `production_depth_four_kernel` holds exactly.

  (III) honesty check: even Stepanov-strength M = 4*n^(2/3) does NOT close depth five
        through the same chain (r5 <= M*n^3 + n*(M*n+3n)); the gap is ~2^26.

  (IV)  small-instance sanity of the counting lemmas: sum_c pairCount = n^2,
        quadCount = conv(pairCount, pairCount), sum_a quadCount = n^4,
        J_4 = sum_a quadCount^2 <= (max_{c!=0} pairCount + 1) * n^6,
        exhaustively on the multiplicative subgroups mu_4 in F_13 and mu_6 in F_31.
"""

import math


def dfact_odd(r: int) -> int:
    v = 1
    for i in range(1, r + 1):
        v *= 2 * i - 1
    return v


def check_cutoffs():
    n, r = 2**30, 110
    budget = dfact_odd(r) * n**r
    expected_sign = {2: -1, 3: -1, 4: +1, 5: +1}
    for s in range(2, 6):
        t = r - s
        J = n ** (2 * s - 1)
        sharp = J * math.comb(r, s) ** 2 * math.factorial(t) * n**t
        coarse = J * math.perm(r, s) ** 2 * math.factorial(t) * n**t
        sign = +1 if sharp > budget else -1
        assert sign == expected_sign[s], (s, math.log2(sharp / budget))
        print(
            f"(I) s={s}: log2(sharp/budget)={math.log2(sharp/budget):+7.2f}  "
            f"log2(coarse/budget)={math.log2(coarse/budget):+7.2f}"
        )


def check_kernel():
    n, r, s = 2**30, 110, 4
    t = r - s
    J = (n // 5 + 1) * n**6
    lhs = J * (math.comb(r, s) ** 2 * (math.factorial(t) * n**t))
    rhs = dfact_odd(r) * n**r
    assert lhs <= rhs
    print(f"(II) production_depth_four_kernel holds: log2 margin={math.log2(rhs/lhs):.3f}")


def check_depth_five_honest():
    n, r = 2**30, 110
    budget = dfact_odd(r) * n**r
    M = 4 * round(n ** (2 / 3))
    J5 = (M * n**3 + n * (M * n + 3 * n)) * n**5
    e5 = J5 * math.comb(r, 5) ** 2 * math.factorial(r - 5) * n ** (r - 5)
    assert e5 > budget
    print(f"(III) depth five NOT closed even at Stepanov strength: log2 over={math.log2(e5/budget):.1f}")


def check_small_instances():
    for p, g, n in ((13, 5, 4), (31, 6, 6)):
        H = sorted({pow(g, k, p) for k in range(n)})
        assert len(H) == n
        pair = {c: 0 for c in range(p)}
        for a in H:
            for b in H:
                pair[(a + b) % p] += 1
        assert sum(pair.values()) == n**2
        quad = {c: 0 for c in range(p)}
        for a in H:
            for b in H:
                for c in H:
                    for d in H:
                        quad[(a + b + c + d) % p] += 1
        assert sum(quad.values()) == n**4
        for a in range(p):
            conv = sum(pair[c] * pair[(a - c) % p] for c in range(p))
            assert conv == quad[a], (p, a)
        M = max(v for c, v in pair.items() if c != 0)
        J4 = sum(v * v for v in quad.values())
        assert all(quad[a] <= (M + 1) * n**2 for a in range(p))
        assert J4 <= (M + 1) * n**6
        print(f"(IV) p={p} n={n}: conv identity exact, M={M}, J4={J4} <= {(M+1)*n**6}")


def main():
    check_cutoffs()
    check_kernel()
    check_depth_five_honest()
    check_small_instances()
    print("VERDICT: depth four reduces to factor-5 pair-sum concentration; depth five stays open")


if __name__ == "__main__":
    main()
