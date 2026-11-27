#!/usr/bin/env python3
"""Independent verification probe for EighthSuccessorTightWindow.

Verifies:
1. Exact tight residual & non-exceptional windows at e = 671,088,640 under BOTH:
   - Pure L1+L2 algebraic model (logarithmic derivations + multi-tier Veronese polars,
     zero Gauss-graph / sparse Bezout dependency),
   - Sparse-Gauss + 3-tier polar model ((2,1), (3,2), (4,2)).
2. Sharpened double-site orbit floor B for saturated quartets at e = 671,088,640
   (267,295,101 under pure L1+L2; 268,236,769 under Sparse-Gauss — within 198,685
   of the 2-to-1 threshold 2d = 268,435,454 out of 4d = 536,870,908 double sites,
   a 51.8x tightening over main).
3. Non-exceptional climb windows above 671,088,640:
   - On all 4 windows, 15c > 3n + 20d and 13c > 3n + 13d force all j>=6 rich heads
     collinear and force every j=5 rich family to contain 4 collinear heads. At 5k
     (W0 & W1), 4+1 is explicitly capped at 2,058,021,547 (EighthFourPlusOne.lean);
     above 5k (W2 & W3), 4+1 and 3+1 remain open.
   - e = 677,600,000 (+6.51M past 5k): all j<=3, all j>=6 (collinear), collinear
     j=4,5, and all j=4 noncollinear with D3>=2 or D4>=6 fit <= 2n.
   - e = 679,477,247 (one error below the 679,477,248 attack): all j<=3, all j>=6
     (collinear), collinear j=4,5, and all j=4 noncollinear with D3>=2 or D4>=7 fit <= 2n.
"""
from math import comb

N = 2**30
K = 2**27
D = K - 1
BUDGET = 2 * N


def surplus(shape, t):
    r, v, s = shape
    mon = sum((s - j + 1) * max(0, r * t - j * D) for j in range(v + 1) if s >= j)
    rows = N * sum((r - i) * (s + 1 - i) for i in range(r))
    return mon - rows


def polar_gap(s_pol, a_pol, t):
    h = comb(s_pol + 2, 2)
    E_pol = s_pol * (s_pol + 1) * (s_pol + 2) // 3
    return a_pol * h * t - comb(a_pol + 2, 3) * N - E_pol * D


def component_cap(b, m, W, t, use_sg, polar_pairs):
    gz = (2 * b - 2) * m - b * (b - 1)
    if use_sg:
        height = m * ((6 * b + 2) * W - 3 * b * b * D)
    else:
        ax = (2 * b - 2) * W - b * (b - 1) * D
        height = 2 * ax * gz + 2 * W * m
    loss = (gz + m) * N
    pop = (2 * t * loss + N * (2 * height + m * N)) // (t * t - N * D)
    for (s_pol, a_pol) in polar_pairs:
        if m > s_pol * (s_pol - 1):
            gap = polar_gap(s_pol, a_pol, t)
            if gap > 0:
                h = comb(s_pol + 2, 2)
                bez = s_pol * b * (2 * m - b - 1) if use_sg else s_pol * m * (m - 1)
                cand = bez + h * (a_pol * loss + s_pol * height) // gap
                if cand < pop:
                    pop = cand
    return gz + 2 * b * m + pop


def collinear_mass(j, e, c):
    den = c + (j - 1) * D
    u = (j * c * c + den - 1) // den
    for a in range(1, j + 1):
        num = 2 * a * j * c - j * (j - 1) * D
        if num > 0:
            u = max(u, (num + a * (a + 1) - 1) // (a * (a + 1)))
    return min(j * (e + 1), j * N - (j - 1) * u)


def check_window(label, e, pri, comp, H, use_sg, polar_pairs, check_1116=True):
    t = N - e
    r1, v1, s1 = pri
    r2, v2, s2 = comp
    sp1, sp2 = surplus(pri, t), surplus(comp, t)
    assert sp1 > 0, f"{label}: pri surplus={sp1}"
    assert sp2 > 0, f"{label}: comp surplus={sp2}"
    assert H >= max(s1, s2), f"{label}: H={H} < max({s1},{s2})"
    assert t * t > N * D, f"{label}: below Johnson"
    c = t - e // H
    assert 15 * c > 3 * N + 20 * D, f"{label}: 15c check failed"
    assert 13 * c > 3 * N + 13 * D, f"{label}: 13c check failed"
    for (sp, ap) in polar_pairs:
        assert polar_gap(sp, ap, t) > 0, f"{label}: polar ({sp},{ap}) gap <= 0"

    # Nonaffine linear multiplier
    lin_mult = 2
    while N // lin_mult + 3 * N // (lin_mult - 1) >= t - D:
        lin_mult += 1
    assert lin_mult * (lin_mult - 1) * (t - D) > (4 * lin_mult - 1) * N

    noncommon = s1 * v2 + v1 * s2
    res_by_j = {}
    for j in range(v1 + 1):
        m_rem = s2 - j
        b_max = v1 - j
        W = r1 * t - 1 - j * D
        max_u = lin_mult
        for m0 in range(2, m_rem + 1):
            for b0 in range(2, min(b_max, m0) + 1):
                if W < b0 * D:
                    continue
                cap = component_cap(b0, m0, W, t, use_sg, polar_pairs)
                u = (cap + m0 - 1) // m0
                if u > max_u:
                    max_u = u
        res_by_j[j] = (s1 + noncommon + (v1 - j) * H + m_rem * max_u, max_u)

    worst_small = max(j * (e + 1) + res_by_j[j][0] for j in range(4))
    worst_col = max(collinear_mass(j, e, c) + res_by_j[j][0] for j in range(4, v1 + 1))
    j5_4p1 = 2_058_021_547 + res_by_j[5][0] if e <= 671_088_640 else 0
    j4_1122 = 2 * (e + 1) + 2 * (1 + e // 2) + res_by_j[4][0]
    j4_1116 = 3 * (e + 1) + (1 + e // 6) + res_by_j[4][0]
    j4_1117 = 3 * (e + 1) + (1 + e // 7) + res_by_j[4][0]

    assert worst_small <= BUDGET, (label, worst_small)
    assert worst_col <= BUDGET, (label, worst_col)
    if e <= 671_088_640:
        assert j5_4p1 <= j4_1116 <= BUDGET, (label, j5_4p1, j4_1116)
    assert j4_1122 <= BUDGET, (label, j4_1122)
    assert j4_1117 <= BUDGET, (label, j4_1117)
    if check_1116:
        assert j4_1116 <= BUDGET, (label, j4_1116)

    B_floor = (BUDGET - 3 * (N - 4 * D) - res_by_j[4][0]) // 2 + 1
    print(
        f"[PASS] {label:28s} e={e:11,d} H={H:4d} lin={lin_mult} | "
        f"res4={res_by_j[4][0]:9,d} (u={res_by_j[4][1]:5d}) | "
        f"j<=3:{worst_small:13,d} col:{worst_col:13,d} | "
        f"1116:{j4_1116:13,d} 1117:{j4_1117:13,d} | B>={B_floor:,d}"
    )
    return res_by_j[4][0], B_floor


if __name__ == "__main__":
    polars_sg = [(2, 1), (3, 2), (4, 2)]
    polars_l12 = [(2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4), (8, 5), (9, 5), (10, 6), (11, 7)]

    r_l12, b_l12 = check_window(
        "671M Pure L1+L2", 671_088_640, (6, 16, 335), (10, 29, 126), 1000, False, polars_l12, True
    )
    r_sg, b_sg = check_window(
        "671M Sparse-Gauss", 671_088_640, (6, 16, 335), (10, 29, 126), 500, True, polars_sg, True
    )
    assert r_l12 == 2_280_700 and b_l12 == 267_295_101
    assert r_sg == 397_364 and b_sg == 268_236_769
    assert 2 * D - b_sg == 198_685

    check_window(
        "677.6M Climb (SG, 1116 OK)", 677_600_000, (8, 22, 950), (14, 41, 237), 1000, True, polars_sg, True
    )
    check_window(
        "679.477M Ceiling-1 (SG)", 679_477_247, (9, 25, 887), (15, 44, 297), 2000, True, polars_sg, False
    )
    print("ALL TIGHT-WINDOW CHECKS PASSED")
