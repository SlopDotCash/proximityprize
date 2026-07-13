#!/usr/bin/env python3
"""G268 exact probe: antipodal floor and sponsor wraparound deficit.

All arithmetic is exact Python int. No FFT, floats are used only for human-readable ratios.
The probe:
  1. derives the local imbalance polynomials by enumerating all 16 A/B membership patterns;
  2. extracts the complete antipodal counts J5^0,J6^0 and checks the closed formulas;
  3. independently brute-forces the abstract antipodal condition at n=8;
  4. recomputes the genuine finite-field cell (n,p)=(32,70753) with exact subset DP and
     multiplicative-orbit compression;
  5. checks the four sponsor inequalities kernel-checked in the companion Lean file.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations
from math import comb

Poly = dict[tuple[int, int], int]


def poly_mul(a: Poly, b: Poly, cap: int) -> Poly:
    out: dict[tuple[int, int], int] = defaultdict(int)
    for (i, j), x in a.items():
        for (k, ell), y in b.items():
            if i + k <= cap and j + ell <= cap:
                out[i + k, j + ell] += x * y
    return dict(out)


def poly_pow(a: Poly, e: int, cap: int) -> Poly:
    out: Poly = {(0, 0): 1}
    base = a
    while e:
        if e & 1:
            out = poly_mul(out, base, cap)
        base = poly_mul(base, base, cap)
        e //= 2
    return out


def local_polynomials() -> dict[int, Poly]:
    out: dict[int, dict[tuple[int, int], int]] = defaultdict(lambda: defaultdict(int))
    for bp in (0, 1):
        for bm in (0, 1):
            for ap in (0, 1):
                for am in (0, 1):
                    imbalance = bp - bm - ap + am
                    out[imbalance][bp + bm, ap + am] += 1
    return {d: dict(p) for d, p in out.items()}


LOCAL = local_polynomials()
P0 = LOCAL[0]
P1 = LOCAL[1]
P2 = LOCAL[2]


def antipodal_transfer(n: int, r: int) -> int:
    assert n % 2 == 0 and n >= 2 * r + 2
    m = n // 2
    first = poly_mul(P1, poly_pow(P0, m - 1, r), r).get((r - 1, r), 0)
    second = poly_mul(poly_mul(P2, P1, r), poly_pow(P0, m - 2, r), r).get(
        (r - 1, r), 0
    )
    return n * (first + 2 * (m - 1) * second)


def antipodal_closed(n: int, r: int) -> int:
    m = n // 2
    if r == 5:
        return n * (m - 2) * (m - 1) * (203 * m * m - 1099 * m + 1536) // 12
    if r == 6:
        return (
            n
            * (m - 2)
            * (m - 1)
            * (287 * m**3 - 2789 * m * m + 9174 * m - 10160)
            // 20
        )
    raise ValueError(r)


def brute_antipodal(n: int, r: int) -> int:
    """Independent abstract enumeration, used only at n=8."""
    half = n // 2
    As = list(combinations(range(n), r))
    Bs = list(combinations(range(n), r - 1))
    total = 0
    for y in range(n):
        for z in range(n):
            for A in As:
                negA = [(-a) % n for a in A]
                for B in Bs:
                    counts = Counter((y, y, *B, (-z) % n, *negA))
                    if all(counts[x] == counts[x + half] for x in range(half)):
                        total += 1
    return total


def prime_factors(x: int) -> list[int]:
    out = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def subgroup(p: int, n: int) -> list[int]:
    root = primitive_root(p)
    zeta = pow(root, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * zeta % p
    assert x == 1 and len(set(out)) == n
    return out


def exact_alignments(n: int, p: int) -> tuple[int, int]:
    """Exact adjacent-rank alignments, orbit-compressed after subset DP."""
    G = subgroup(p, n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1

    hist = [[0] * p for _ in range(7)]
    hist[0][0] = 1
    for used, x in enumerate(G, 1):
        for k in range(min(6, used), 0, -1):
            src, dst = hist[k - 1], hist[k]
            for s, value in enumerate(src):
                if value:
                    dst[(s + x) % p] += value

    seen = bytearray(p)
    reps = [0] if W[0] else []
    for x in range(1, p):
        if W[x] and not seen[x]:
            reps.append(x)
            for g in G:
                seen[x * g % p] = 1

    ans = []
    for r in (5, 6):
        dot = 0
        for x in reps:
            rx = sum(hist[r][s] * hist[r - 1][(s - x) % p] for s in range(p))
            dot += W[x] * rx * (1 if x == 0 else n)
        mass = n * n * comb(n, r) * comb(n, r - 1)
        ans.append(p * dot - mass)
    return ans[0], ans[1]


def main() -> None:
    expected = {
        0: {(0, 0): 1, (0, 2): 1, (1, 1): 2, (2, 0): 1, (2, 2): 1},
        1: {(0, 1): 1, (1, 0): 1, (1, 2): 1, (2, 1): 1},
        2: {(1, 1): 1},
    }
    for d in (0, 1, 2):
        assert LOCAL[d] == expected[d]
        assert LOCAL[-d] == expected[d]
    print("local transfer polynomials: P0,P±1,P±2 exact (16/16 patterns)")

    for n0 in (8, 16, 32, 64, 128):
        for r in (5, 6):
            if n0 >= 2 * r + 2:
                assert antipodal_transfer(n0, r) == antipodal_closed(n0, r)
    # The n=8 direct enumeration is still meaningful at r=5,6 even though 2r+2<n fails;
    # it tests the pairing-count combinatorics itself, not Lam-Leung completeness.
    for r, want in ((5, 1552), (6, 672)):
        got = brute_antipodal(8, r)
        assert got == want == antipodal_closed(8, r)
    print("independent n=8 antipodal brute force: J5=1552, J6=672")

    good_a5, good_a6 = exact_alignments(8, 2969)
    for r, alignment in ((5, good_a5), (6, good_a6)):
        mass = 8**2 * comb(8, r) * comb(8, r - 1)
        assert (alignment + mass) % 2969 == 0
        assert (alignment + mass) // 2969 == antipodal_closed(8, r)
    print("good-prime check: n=8 p=2969 actual J5,J6 equal the antipodal baselines")

    a5, a6 = exact_alignments(32, 70753)
    assert (a5, a6) == (132970510400, -1324791182208)
    assert 69 * 32**2 < 70753 - 1
    print(f"cross-scale exact cell: n=32 p=70753 tau={(70753-1)/32**2} A5={a5} A6={a6}")

    n0 = 2**30
    m0 = n0 // 2
    p1 = n0 * (2**128 + 192) + 1
    p2 = n0 * (2**129 + 13) + 1
    j5 = antipodal_closed(n0, 5)
    j6 = antipodal_closed(n0, 6)
    b5 = n0 * n0 * comb(n0, 5) * comb(n0, 4)
    b6 = n0 * n0 * comb(n0, 6) * comb(n0, 5)
    assert p1 * (2**10 * j5) < b5
    assert p2 * (2**9 * j5) < b5
    assert p1 * (2**36 * j6) < b6
    assert p2 * (2**35 * j6) < b6
    print("sponsor exact deficits:")
    print(f"  P1 rank5 B/(pJ0)={b5/(p1*j5):.12g}; P2={b5/(p2*j5):.12g}")
    print(f"  P1 rank6 B/(pJ0)={b6/(p1*j6):.12g}; P2={b6/(p2*j6):.12g}")
    print("G268 PASS: full antipodal supply is production-insufficient; wraparound excess is load-bearing.")


if __name__ == "__main__":
    main()
