#!/usr/bin/env python3
"""Independent exact-integer verifier for FirstPrimeHalfBlowupClimb.lean
(e = 312,400,000 half-rate errors on the first designated prime, B_1 = 2^30)."""
from math import comb

N = 2**30
BUDGET = N
P1 = 2**30 * (2**128 + 192) + 1
D = N // 2 - 1
E = 312_400_000
T = N - E
MISS = 7000
CORE = T - MISS
PRIMARY = (54, 76, 44_746)
COMPANION = (102, 144, 5_412)
BOUND3 = 1_067_196_929
NON_HEAD_BOUND4 = 126_933_994
VERONESE = ((6, 5), (12, 10), (24, 20))
ALPHA0 = 52_991
BETA0 = 14_109


def require(cond, msg):
    if not cond:
        raise ValueError(msg)


def ceil_div(a, b):
    require(b > 0, 'positive divisor')
    return (a + b - 1) // b


def surplus(shape):
    r, v, s = shape
    cols = sum((s + 1 - j) * max(0, r * T - j * D) for j in range(v + 1))
    rows = N * sum((r - j) * (s + 1 - j) for j in range(r))
    return cols - rows


def discrete_union(j):
    cands = [a for a in (7 * j // 10, (7 * j + 9) // 10) if 1 <= a < j]
    require(cands, f'valid discrete parameter for j={j}')
    return max(ceil_div(2 * a * j * CORE - j * (j - 1) * D, a * (a + 1)) for a in cands)


def head_mass(j):
    if j < 3:
        return j * (E + 1)
    u = max(discrete_union(j), ceil_div(j * CORE * CORE, CORE + (j - 1) * D))
    return min(j * (E + 1), max(0, j * N - (j - 1) * u))


def blowup_h(b, w):
    require(b * D <= w <= b * T - 1, f'admissible weight b={b} w={w}')
    wt = max(0, w - T)
    return (6 * b + 2) * w - 3 * b * b * D - (3 * wt * wt) // T - 2 * wt


def factor_unit_price(j, b, m):
    w_max = PRIMARY[0] * T - 1 - j * D
    w = min(w_max, b * T - 1)
    hb = blowup_h(b, w)
    rb = (2 * b - 1) * N
    p = min(j, 2)
    tri = 2 * b + ceil_div((3 - p) * (rb + hb), 3 * T - (N + 2 * D + p * MISS))
    best = tri
    if j >= 3:
        gap = T + discrete_union(j) - (N + D)
        require(gap > 0, f'positive transverse gap at j={j}')
        best = min(best, 2 * b + ceil_div(hb + rb, gap))
    if j == 0:
        for s, a in VERONESE:
            if m > s * (s - 1):
                h = comb(s + 2, 2)
                gap = a * h * T - comb(a + 2, 3) * N - (s * (s + 1) * (s + 2) // 3) * D
                require(gap > 0, f'positive Veronese gap ({s},{a})')
                best = min(best, 2 * s * b + ceil_div(h * (a * rb + s * hb), gap))
    return 4 * b - 2 + best


def main():
    require(P1 // 2**128 == BUDGET, 'first prime 128-bit budget')
    sr1, sr2 = surplus(PRIMARY), surplus(COMPANION)
    require((sr1, sr2) == (202_506_832, 7_072_525_648), f'surpluses {(sr1, sr2)}')
    require(N + 2 * D < 3 * CORE and E < MISS * PRIMARY[2] and COMPANION[2] < PRIMARY[2],
            'rich-head extraction and forced collinearity')
    linear = 1 + ceil_div(4 * N, T - D)
    resultant = PRIMARY[1] * COMPANION[2] + PRIMARY[2] * COMPANION[1]
    require((linear, resultant) == (21, 6_854_736), f'linear/resultant {(linear, resultant)}')
    require(2 * PRIMARY[0] * T * PRIMARY[1] < 2**100 < P1 and
            COMPANION[2] * (COMPANION[2] - 1) < 2**100 < P1, 'tame characteristic')

    checked = 0
    # 1. Non-exceptional j = 0..3 safety below BOUND3 < BUDGET
    max_le3 = (0, -1)
    for j in range(4):
        nh_base = PRIMARY[2] + resultant + (PRIMARY[1] - j) * PRIMARY[2] + (COMPANION[2] - j) * linear
        other = head_mass(j) + nh_base
        rem_b = PRIMARY[1] - j
        rem_m = COMPANION[2] - j
        if j == 0:
            a_j, b_j = ALPHA0, BETA0
        else:
            a_j, b_j = (BOUND3 - other) // rem_m, 0
        tot = other + rem_m * a_j + rem_b * b_j
        require(tot <= BOUND3, f'j={j} exceeds BOUND3: {tot}')
        require((COMPANION[2] - j) + (COMPANION[1] - j) <= a_j, f'case1 fallback at j={j}')
        for b in range(2, rem_b + 1):
            for m in (b, 30, 31, 132, 133, 552, 553, rem_m):
                if b <= m <= rem_m:
                    u = factor_unit_price(j, b, m)
                    require(m * u <= m * a_j + b * b_j, f'dual fail j={j} b={b} m={m}')
                    checked += 1
        if j == 0:
            max_le3 = max(max_le3, (tot, j))
        else:
            max_u = max(max(factor_unit_price(j, b, b) for b in range(2, rem_b + 1)),
                        (COMPANION[2] - j) + (COMPANION[1] - j))
            max_le3 = max(max_le3, (other + rem_m * max_u, j))
    require(max_le3 == (BOUND3, 3) and BOUND3 < BUDGET, f'max_le3={max_le3}')

    # 2. Collinear 4 <= j <= 76 uniform non-head ceiling
    max_nh4 = (0, -1)
    for j in range(4, PRIMARY[1] + 1):
        nh_base = PRIMARY[2] + resultant + (PRIMARY[1] - j) * PRIMARY[2] + (COMPANION[2] - j) * linear
        rem_b = PRIMARY[1] - j
        rem_m = COMPANION[2] - j
        a_j = (NON_HEAD_BOUND4 - nh_base) // rem_m
        require(nh_base + rem_m * a_j <= NON_HEAD_BOUND4, f'nh4 fail j={j}')
        if rem_b >= 2:
            require((COMPANION[2] - j) + (COMPANION[1] - j) <= a_j, f'case1 fallback j={j}')
            max_u = (COMPANION[2] - j) + (COMPANION[1] - j)
            for b in range(2, rem_b + 1):
                u = factor_unit_price(j, b, b)
                require(u <= a_j, f'nh4 dual fail j={j} b={b}')
                max_u = max(max_u, u)
                checked += 1
            max_nh4 = max(max_nh4, (nh_base + rem_m * max_u, j))
        else:
            max_nh4 = max(max_nh4, (nh_base, j))
    require(max_nh4 == (NON_HEAD_BOUND4, 4), f'max_nh4={max_nh4}')

    # 3. Four-core pairwise overlap & direction degree cap
    min_overlap = ceil_div(16 * CORE - 6 * N, 12)
    require(min_overlap == 478_242_187, f'min_overlap={min_overlap}')
    max_dir_deg = D - min_overlap
    require(max_dir_deg == 58_628_724, f'max_dir_deg={max_dir_deg}')
    head_floor = BUDGET + 1 - NON_HEAD_BOUND4
    require(head_floor == 946_807_831, f'head_floor={head_floor}')

    print(f'FIRST-PRIME HALF e={E:,}: surpluses=({sr1:,}, {sr2:,}), resultant={resultant:,}, linear={linear}')
    print(f'Verified {checked:,} checks; j<=3 max={BOUND3:,} < B_1={BUDGET:,} (slack={BUDGET - BOUND3:,}).')
    print(f'All 4<=j<=76 non-head max={NON_HEAD_BOUND4:,} => collinear head floor={head_floor:,}, '
          f'min 4-core overlap={min_overlap:,}, max dir deg={max_dir_deg:,}.')


if __name__ == '__main__':
    main()
