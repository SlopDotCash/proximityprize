#!/usr/bin/env python3
"""Exact allocation for two mixed-Hasse surfaces with shared residual degrees."""
from dataclasses import dataclass
from math import comb

N = 1 << 30
P2 = N * (2**129 + 13) + 1


@dataclass(frozen=True)
class Window:
    rate_denominator: int
    errors: int
    primary: tuple[int, int, int]
    companion: tuple[int, int, int]
    rank_surpluses: tuple[int, int]
    bound: int


WINDOWS = (
    Window(2, 313_234_000, (89, 126, 295_664), (174, 246, 14_868),
           (4_238_610, 1_662_163_854), 2_145_566_228),
    Window(4, 534_325_000, (53, 106, 130_044), (104, 208, 7_551),
           (108_222_714, 14_248_080_392), 2_146_821_341),
)


def ceil_div(a, b):
    assert b > 0
    return -(-a // b)


def rank_surplus(shape, t, d):
    r, v, s = shape
    assert 0 < r <= s + 1 and v <= s and v * d < r * t
    columns = sum((s + 1 - i) * (r * t - i * d) for i in range(v + 1))
    rows = sum((s + 1 - i) * (r - i) for i in range(r))
    return columns - N * rows


def head_bounds(j, t, d, miss):
    separate = j * (N - t + 1)
    if j < 3:
        return separate, 0
    core = t - miss
    discrete = max(ceil_div(2 * a * j * core - j * (j - 1) * d, a * (a + 1))
                   for a in range(1, j))
    cover = max(discrete, ceil_div(j * core**2, core + (j - 1) * d))
    return min(separate, max(0, j * N - (j - 1) * cover)), discrete


def prices(window, j, b, t, d, miss, union):
    r1, _, _ = window.primary
    _, v2, s2 = window.companion
    w = min(r1 * t - 1 - j * d, b * t - 1)
    assert b * d <= w
    excess = max(0, w - t)
    height = (6 * b + 2) * w - 3 * b * b * d - 3 * excess**2 // t - 2 * excess
    losses = (2 * b - 1) * N
    fixed = min(j, 2)
    triangle_gap = 3 * t - N - 2 * d - fixed * miss
    best = 6 * b - 2 + ceil_div((3 - fixed) * (losses + height), triangle_gap)
    half = window.rate_denominator == 2
    if j >= (3 if half else 4):
        transverse_gap = t + union - N - d
        best = min(best, 6 * b - 2 + ceil_div(losses + height, transverse_gap))

    fallback = s2 + v2 - 2 * j
    regimes = [(0, max(best, fallback))]
    if j <= (0 if half else 3):
        levels = ((6, 5), (12, 10), (24, 20)) if half else ((4, 3), (8, 6), (16, 11), (24, 17))
        fixed = min(j, 3)
        for degree, order in levels:
            h = comb(degree + 2, 2)
            gap = (order * h * t - comb(order + 2, 3) * N
                   - degree * (degree + 1) * (degree + 2) // 3 * d - order * fixed * miss)
            veronese = (4 * b - 2 + 2 * degree * b
                        + ceil_div((h - fixed) * (order * losses + degree * height), gap))
            best = min(best, veronese)
            regimes.append((degree * (degree - 1), max(best, fallback)))

    alpha = regimes[-1][1]
    beta = max([0] + [ceil_div(guard * (unit - alpha), b)
                      for (_, unit), (guard, _) in zip(regimes, regimes[1:])])
    for (_, unit), (guard, _) in zip(regimes, regimes[1:]):
        assert (unit - alpha) * guard <= beta * b
    return alpha, beta


def allocation(window):
    t = N - window.errors
    d = N // window.rate_denominator - 1
    r1, v1, s1 = window.primary
    _, v2, s2 = window.companion
    assert v1 <= v2 and s2 < s1
    assert tuple(rank_surplus(s, t, d) for s in (window.primary, window.companion)) == window.rank_surpluses
    assert min(window.rank_surpluses) > 0
    miss = window.errors // s1 + 1
    assert window.errors < miss * s1 and 3 * (t - miss) > N + 2 * d
    assert max(2 * r1 * t * v1, s2 * (s2 - 1)) < P2
    linear = 1 + ceil_div(4 * N, t - d)
    checked = 0
    peak = (-1, 0, 0)
    for j in range(v1 + 1):
        heads, union = head_bounds(j, t, d, miss)
        # No common nonlinear factor carries a selected section.
        empty = heads + s1 + (s1 - j) * (v2 - j) + (v1 - j) * (s2 - j + s1) + linear * (s2 - j)
        peak = max(peak, (empty, j, 0))
        alpha = beta = 0
        for c in range(2, v1 - j + 1):
            price, surcharge = prices(window, j, c, t, d, miss, union)
            alpha, beta = max(alpha, price), max(beta, surcharge)
            u = v1 - j - c
            residual_y = v2 - j - c
            base = heads + s1 + (s2 - j) * alpha + (v1 - j) * beta
            if u == 1:
                # All remaining positive-ordinate factors fit in one linear factor.
                assert alpha >= linear
                base += max(s1, linear * (s1 - s2))
            elif u >= 2:
                assert alpha >= residual_y + u + linear
                # Maximum of the relative residual charge over the unused plane degree.
                base += u * s1 + max(0, (s1 - s2 + residual_y + u + linear - alpha) * residual_y)
            peak = max(peak, (base, j, c))
            checked += 1
    assert peak[0] == window.bound < 2 * N
    return checked, peak


if __name__ == "__main__":
    for entry in WINDOWS:
        combinations, (cap, heads, max_ordinate) = allocation(entry)
        print(f"1/{entry.rate_denominator}, {entry.errors:,} errors: "
              f"{combinations:,} (j,c) cases, bound {cap:,}, slack {2*N - cap:,}, "
              f"peak j={heads}, c={max_ordinate}.")
