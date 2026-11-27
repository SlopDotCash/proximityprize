#!/usr/bin/env python3
"""Independent exact-integer verifier for the blown-up Gauss-graph half-rate window
at e = 313,215,000 errors (second designated prime, n = 2^30, rate 1/2)."""
from math import comb

N = 2**30
BUDGET = 2 * N
P2 = 2**30 * (2**129 + 13) + 1
D = N // 2 - 1
E = 313_215_000
T = N - E
MISS = 4096
CORE = T - MISS
PRIMARY = (88, 124, 188_604)
COMPANION = (174, 246, 14_431)
BOUND = 2_145_744_452
VERONESE = ((6, 5), (12, 10), (24, 20))
ALPHA0 = 131_427
BETA0 = 27_182


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
    sr1, sr2 = surplus(PRIMARY), surplus(COMPANION)
    require((sr1, sr2) == (152_825_916, 13_495_881_357), f'surpluses {(sr1, sr2)}')
    require(N + 2 * D < 3 * CORE and E < MISS * PRIMARY[2] and COMPANION[2] < PRIMARY[2],
            'rich-head extraction and collinearity')
    linear = 1 + ceil_div(4 * N, T - D)
    resultant = PRIMARY[1] * COMPANION[2] + PRIMARY[2] * COMPANION[1]
    require((linear, resultant) == (21, 48_186_028), f'linear/resultant {(linear, resultant)}')
    require(2 * PRIMARY[0] * T * PRIMARY[1] < P2 and COMPANION[2] * (COMPANION[2] - 1) < P2,
            'tame characteristic')

    worst = (0, -1)
    checked_pairs = 0
    for j in range(PRIMARY[1] + 1):
        other = (head_mass(j) + PRIMARY[2] + resultant
                 + (PRIMARY[1] - j) * PRIMARY[2] + (COMPANION[2] - j) * linear)
        rem_b = PRIMARY[1] - j
        rem_m = COMPANION[2] - j
        if j == 0:
            a_j, b_j = ALPHA0, BETA0
        else:
            a_j, b_j = (BOUND - other) // rem_m, 0
        tot = other + rem_m * a_j + rem_b * b_j
        require(tot <= BOUND, f'budget at j={j}: {tot}')
        if rem_b >= 2:
            require((COMPANION[2] - j) + (COMPANION[1] - j) <= a_j, f'case1 fallback at j={j}')
            # Exhaustively check every admissible (b, m) regime endpoint!
            for b in range(2, rem_b + 1):
                for m in (b, 30, 31, 132, 133, 552, 553, rem_m):
                    if b <= m <= rem_m:
                        u = factor_unit_price(j, b, m)
                        require(m * u <= m * a_j + b * b_j, f'dual price fail j={j} b={b} m={m}')
                        checked_pairs += 1
        if j == 0:
            worst = max(worst, (tot, j))
        elif rem_b >= 2:
            # Exact max over b of base price for j >= 1
            max_u = max(factor_unit_price(j, b, b) for b in range(2, rem_b + 1))
            max_u = max(max_u, (COMPANION[2] - j) + (COMPANION[1] - j))
            worst = max(worst, (other + rem_m * max_u, j))
        else:
            worst = max(worst, (other, j))

    require(worst == (BOUND, 4) and BOUND < BUDGET, f'worst={worst}')
    print(f'HALF e={E:,}: surpluses=({sr1:,}, {sr2:,}), resultant={resultant:,}, linear={linear}')
    print(f'Verified {checked_pairs:,} (j, b, m) checks; max={BOUND:,} at j=4, slack={BUDGET - BOUND:,}.')


if __name__ == '__main__':
    main()
