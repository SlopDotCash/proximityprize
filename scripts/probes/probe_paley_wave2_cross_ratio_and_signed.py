#!/usr/bin/env python3
"""Exact verifier for Wave 2 CORE Paley Lean modules:
  1. PaleyCrossRatioBarrier.lean (quartic-to-Legendre, unsigned cross-ratio barrier,
     dyadic DFT even/odd Parseval energy split, 5-site skew F3-rank constancy),
  2. PaleySignedHankelDegree.lean / PaleySignedSquareRoot.lean /
     PaleyFourSiteRankAndOverlap.lean (finite signed row budgets, central multiplicities,
     p = 65537 bounds 56,829 & 142,536,640, skew-prime overlap improvement).
"""

from cmath import exp, pi
from itertools import combinations, permutations, product
from math import comb, isqrt, sqrt


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def legendre_trace(lam, p):
    return sum(legendre(z * (z - 1) * (z - lam), p) for z in range(p))


def test_quartic_cross_ratio_identity():
    checked = 0
    for p in (7, 11, 13, 17):
        L = {lam: legendre_trace(lam, p) for lam in range(p)}
        for a, b, c, d in combinations(range(p), 4):
            lhs = sum(legendre((x - a) * (x - b) * (x - c) * (x - d), p) for x in range(p))
            lam = ((a - c) * (b - d) * pow((a - b) * (c - d), -1, p)) % p
            rhs = -1 + legendre(-(a - b) * (c - d), p) * L[lam]
            assert lhs == rhs, f"quartic mismatch p={p}, {(a, b, c, d)}: {lhs} != {rhs}"
            checked += 1
    print(f"[PASS] Suite 1: quartic_charSum_eq_legendreTrace exact on {checked} quadruples (p=7,11,13,17)")


def test_unsigned_cross_ratio_barrier():
    checked = 0
    for p in (11, 13, 17, 19, 29, 37):
        for n in (4, 5, 6, min(9, p - 2)):
            A = list(range(n))
            counts = {}
            for a, b, c, d in permutations(A, 4):
                lam = ((a - c) * (b - d) * pow((a - b) * (c - d), -1, p)) % p
                assert lam not in (0, 1)
                counts[lam] = counts.get(lam, 0) + 1
            n4 = n * (n - 1) * (n - 2) * (n - 3)
            assert sum(counts.values()) == n4
            energy = sum(v * v for v in counts.values())
            assert (p - 2) * energy >= n4 * n4
            assert p * sqrt(energy) >= sqrt(p) * n4 - 1e-9
            checked += 1
    print(f"[PASS] Suite 2: unsigned_crossRatio_energy_ge & Hasse barrier verified on {checked} cases")


def test_dyadic_dft_parseval_split():
    checked = 0
    for p in (17, 41, 73, 97, 113, 193, 257):
        # Find primitive element
        g0 = next(x for x in range(2, p) if len({pow(x, k, p) for k in range(p - 1)}) == p - 1)
        # Test every even subgroup order 2m | (p - 1)
        for m in range(1, (p - 1) // 2 + 1):
            if (p - 1) % (2 * m) != 0:
                continue
            g = pow(g0, (p - 1) // (2 * m), p)
            assert pow(g, m, p) == p - 1
            c = [legendre(1 - pow(g, j, p), p) for j in range(2 * m)]
            s_sq = sum(legendre(1 - pow(g, 2 * j, p), p) for j in range(m))
            dft = [
                sum(c[j] * exp(2j * pi * k * j / (2 * m)) for j in range(2 * m))
                for k in range(2 * m)
            ]
            even_energy = sum(abs(dft[2 * r]) ** 2 for r in range(m))
            odd_energy = sum(abs(dft[2 * r + 1]) ** 2 for r in range(m))
            expected_even = m * (2 * m - 1 + 2 * s_sq)
            expected_odd = m * (2 * m - 1 - 2 * s_sq)
            assert abs(even_energy - expected_even) < 1e-7, (p, m, even_energy, expected_even)
            assert abs(odd_energy - expected_odd) < 1e-7, (p, m, odd_energy, expected_odd)
            checked += 1
    print(f"[PASS] Suite 3: dyadic_dft_even_energy & odd_energy exact on {checked} subgroups")


def rank_f3(M):
    n = len(M)
    A = [[x % 3 for x in row] for row in M]
    r = 0
    for col in range(n):
        piv = next((i for i in range(r, n) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = 1 if A[r][col] == 1 else 2
        A[r] = [(x * inv) % 3 for x in A[r]]
        for i in range(n):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [(A[i][j] - f * A[r][j]) % 3 for j in range(n)]
        r += 1
    return r


def test_skew_five_f3_rank():
    # Exhaustive check over all 2^6 = 64 normalized 5x5 skew-symmetric zero-diag {±1} matrices over F3
    checked = 0
    for bits in product((1, 2), repeat=6):
        M = [[0] * 5 for _ in range(5)]
        for j in range(1, 5):
            M[0][j] = 1
            M[j][0] = 2
        pairs = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
        for (i, j), val in zip(pairs, bits):
            M[i][j] = val
            M[j][i] = (-val) % 3
        assert rank_f3(M) == 4
        checked += 1
    assert checked == 64
    print(f"[PASS] Suite 4: skew_five_f3_rank_eq_four verified exhaustively on all {checked}/64 switching classes")


def test_65537_and_skew_overlap():
    # Exact check of p = 65537, n = 256 bounds matching Lean theorems
    p = 65537
    d = p // 2
    a = b = 256
    x_rect = 64
    rhs_rect = b * b * (a - 2 * x_rect) ** 2 + 4 * b * x_rect * (d + a - 2 * x_rect)
    assert rhs_rect == 3_229_614_080
    assert isqrt(rhs_rect) == 56_829

    n = 256
    x_rank = 63
    U_x = n * ((n - 1) * (n - 2 - 2 * x_rank) ** 2 + (n - 1 - 2 * x_rank) ** 2 + 4 * x_rank * (d + n - 1 - 2 * x_rank))
    assert U_x == 3_196_058_880
    R = n * (n - 1) * (2 * n - 3)
    C4 = comb(n, 4)
    assert C4 == 174_792_640
    N4_max = (8 * C4 + U_x - R) // 32
    assert N4_max == 142_536_640

    # Exact check of skew-prime overlap bound on p = 19, 23, 31
    overlap_checked = 0
    for p3 in (19, 23, 31):
        assert legendre(-1, p3) == -1
        m = isqrt(p3) + 1
        for k in range(1, m):
            A = set(range(m))
            B = set(range(m - k, 2 * m - k))
            C = A & B
            assert len(C) == k
            S = sum(legendre(u - t, p3) for u in A for t in B)
            M = sum(sum(legendre(u - t, p3) for u in A) ** 2 for t in B)
            assert abs(S) <= m * m - k * k
            uMax = k * (m - k)
            if uMax * uMax * m <= k * k * M:
                rhs = uMax + sqrt((m - k) * (M - k * (m - k) ** 2))
                assert abs(S) <= rhs + 1e-9
            overlap_checked += 1
    print(
        f"[PASS] Suite 5: p=65537 bounds (56,829 & 142,536,640) and {overlap_checked} skew-overlap checks exact"
    )


if __name__ == "__main__":
    test_quartic_cross_ratio_identity()
    test_unsigned_cross_ratio_barrier()
    test_dyadic_dft_parseval_split()
    test_skew_five_f3_rank()
    test_65537_and_skew_overlap()
