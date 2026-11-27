#!/usr/bin/env python3
"""Verify two all-pair MCA bounds from conditioned surfaces and global multiplicities."""

from dataclasses import dataclass
from itertools import product
from math import comb
from fractions import Fraction

from probe_shared_factor_degrees import N, P2, ceil_div, head_bounds


HEAD_CUTOFF = 500_000


@dataclass(frozen=True)
class Window:
    rate: int
    errors: int
    orders: tuple[int, int]
    plane_degrees: tuple[tuple[int, ...], tuple[int, ...]]
    peak: tuple[int, int, int]
    third_peak: tuple[int, int, int]


WINDOWS = (
    Window(2, 313_250_000, (90, 174), (
        (266426, 260278, 254455, 248957, 243779, 238921),
        (15258, 15019, 14796, 14589, 14400, 14227),
    ), (2145128427, 1, 124), (2145073115, 1, 124)),
    Window(4, 534_425_000, (55, 108), (
        (181766, 176938, 172281, 167795, 163477, 159325),
        (8175, 8028, 7886, 7750, 7619, 7494),
    ), (2145437223, 3, 105), (2145262823, 3, 105)),
)


@dataclass(frozen=True)
class Surface:
    r: int
    v: int
    s: int
    drop: int
    weight: int


def jets(s, r):
    return sum((r - i) * (s + 1 - i) for i in range(r))


def surfaces(w, h, t, d, core):
    result = []
    for index, (r, sizes) in enumerate(zip(w.orders, w.plane_degrees)):
        drop = index + 1 if h else 0
        weight = r * t - h * drop * d
        v = (weight - 1) // d
        s = sizes[h]
        assert 0 < r <= s + 1 and h * drop <= r and v <= s <= HEAD_CUTOFF
        saving = jets(s, r) - jets(s, r - drop)
        pair_cost = drop**2 * (s + 1)
        for owners in range(h + 1):
            assert (jets(s, r - drop * owners) + owners * saving
                    <= jets(s, r) + comb(owners, 2) * pair_cost)
        columns = sum((s + 1 - i) * (weight - i * d) for i in range(v + 1))
        rows = N * jets(s, r) - h * core * saving + comb(h, 2) * d * pair_cost
        assert columns > rows
        assert max(2 * weight * v, s * (s - 1)) < P2
        result.append(Surface(r, v, s, drop, weight))
    return result


def auxiliary_surface(w, primary, h, t, d, core):
    s = 1_000_000
    v = primary.v - int(w.rate == 4)
    r, drop = primary.r, primary.drop
    saving = jets(s, r) - jets(s, r - drop)
    rows = N * jets(s, r) - h * core * saving + comb(h, 2) * d * drop**2 * (s + 1)
    slots = sum(s + 1 - i for i in range(v + 1))
    shift = sum((s + 1 - i) * i * d for i in range(v + 1))
    weight = max(v * d + 1, (rows + shift) // slots + 1)
    assert slots * weight - shift > rows and weight <= primary.weight
    for owners in range(h + 1):
        assert (jets(s, r - drop * owners) + owners * saving
                <= jets(s, r) + comb(owners, 2) * drop**2 * (s + 1))
    return Surface(r, v, s, drop, weight)


def height_bound(w, primary, h, peeled, b, t, d, auxiliary=None):
    max_weight = min(primary.weight - peeled * d - 1, b * t - 1)
    if auxiliary is not None:
        max_weight = min(max_weight, auxiliary.weight - 1)
    assert b * d <= max_weight
    excess = max(0, max_weight - t)
    height = ((6 * b + 2) * max_weight - 3 * b**2 * d
              - (3 * excess**2) // t - 2 * excess)
    deficit = (primary.v * (N - d) - primary.r * w.errors
               + h * primary.drop * (t - 1 - d) - 1 - peeled * (w.errors + 1))
    if auxiliary is not None:
        deficit = min(deficit, auxiliary.v * (N - d) + auxiliary.weight - 1
                      - N * auxiliary.r + h * auxiliary.drop * (t - 1))
    # The global excess above W in the available sum of nef weights.
    extra_capacity = b * (N - d) - deficit - N
    if extra_capacity >= 0 and b * d >= t:
        bonus = max(0, min(2 * (b * d - t), t * extra_capacity // w.errors)
                    - ceil_div(b**2, 4))
        height -= 3 * bonus + 2 * t
    assert height >= 0
    return height


def tangent_prices(w, j, b, t, d, miss, union, height, fallback):
    losses = (2 * b - 1) * N
    fixed = min(j, 2)
    gap = 3 * t - N - 2 * d - fixed * miss
    current = 6 * b - 2 + ceil_div((3 - fixed) * (height + losses), gap)
    if j >= (3 if w.rate == 2 else 4):
        transverse = 6 * b - 2 + ceil_div(height + losses, t + union - N - d)
        current = min(current, transverse)

    regimes = [(0, max(fallback, current))]
    if w.rate == 2 and j == 0:
        levels = ((6, 5), (12, 10), (24, 20))
    elif w.rate == 4 and j <= 3:
        levels = ((4, 3), (8, 6), (16, 11), (24, 17))
    else:
        levels = ()
    p = min(j, 3)
    for degree, order in levels:
        dim = comb(degree + 2, 2)
        energy = degree * (degree + 1) * (degree + 2) // 3
        for multiplicity in range(1, min(order + 1, (degree + 1) // max(1, p)) + 1):
            rows = p * comb(multiplicity + 1, 2)
            derivative_order = p * multiplicity * (multiplicity - 1) * (multiplicity + 1) // 3
            assert rows < dim and p * multiplicity <= degree + 1
            gap = (order * dim * t - comb(order + 2, 3) * N - energy * d
                   - order * rows * miss - derivative_order * (t - miss - d))
            if gap > 0:
                price = (4 * b - 2 + 2 * degree * b
                         + ceil_div((dim - rows) * (order * losses + degree * height), gap))
                current = min(current, price)
            if not p:
                break
        regimes.append((degree * (degree - 1), max(current, fallback)))
    alpha = regimes[-1][1]
    beta = max([0] + [ceil_div(guard * (price - alpha), b)
                      for (_, price), (guard, _) in zip(regimes, regimes[1:])])
    return alpha, beta


def verify(w, with_third=False):
    t = N - w.errors
    d = N // w.rate - 1
    miss = w.errors // HEAD_CUTOFF + 1
    core = t - miss
    assert w.errors < miss * HEAD_CUTOFF and 3 * core > N + 2 * d
    assert P2 // 2**128 == 2 * N
    table = [surfaces(w, h, t, d, core) for h in range(6)]
    third = [auxiliary_surface(w, a, h, t, d, core) for h, (a, _) in enumerate(table)]
    linear = 1 + ceil_div(4 * N, t - d)
    peak = (0, 0, 0)
    checks = 0
    for j in range(table[0][0].v + 1):
        if j >= 2 and j * core**2 > N * (core + (j - 1) * d):
            continue
        h = min(5, j)
        peeled = j - h
        a, bsurf = table[h]
        v, s = a.v - peeled, a.s - peeled
        cv, cs = bsurf.v - peeled, bsurf.s - peeled
        assert 0 <= v <= cv and 0 <= cs <= s
        heads, union = head_bounds(j, t, d, miss)
        empty = heads + s + s * cv + v * (cs + HEAD_CUTOFF) + linear * cs
        peak = max(peak, (empty, j, 0))
        alpha = beta = 0
        for c in range(2, v + 1):
            height = height_bound(w, a, h, peeled, c, t, d)
            unit, surcharge = tangent_prices(w, j, c, t, d, miss, union,
                                            height, cs + cv)
            aux = third[h]
            if with_third and c <= aux.v:
                improved_height = height_bound(w, a, h, peeled, c, t, d, aux)
                better, extra = tangent_prices(w, j, c, t, d, miss, union,
                                               improved_height, cs + cv)
                assert better <= unit
                if better < unit:
                    assert aux.v < better
                    # A coprime third surface costs at most aux.s*c + aux.v*m.
                    # Below m/c = aux.s/(better-aux.v), keep the original price.
                    slope_loss = ceil_div((unit - better) * aux.s, better - aux.v)
                    surcharge = max(extra, surcharge + slope_loss)
                    unit = better
            alpha = max(alpha, unit)
            beta = max(beta, surcharge)
            u, residual = v - c, cv - c
            cost = heads + s + alpha * cs + beta * v
            if u == 1:
                assert alpha >= linear
                cost += max(HEAD_CUTOFF, linear * (s - cs))
            elif u >= 2:
                assert alpha >= residual + u + linear
                cost += u * HEAD_CUTOFF + max(0, (s - cs + residual + u + linear - alpha) * residual)
            peak = max(peak, (cost, j, c))
            checks += 1
    assert peak == (w.third_peak if with_third else w.peak) and peak[0] <= 2 * N
    count = 3 if with_third else 2
    print(f"Rate 1/{w.rate}, {count} surfaces, safe through {w.errors:,}: cap {peak[0]:,}; "
          f"{checks:,} nonlinear cases; maximum at ({peak[1]}, {peak[2]}).")


def check_fill():
    # Small rational controls for the one partially filled bin in the height estimate.
    for caps in product(range(5), repeat=4):
        total = sum(caps)
        for twice_mass in range(2 * total + 1):
            mass = Fraction(twice_mass, 2)
            left = mass
            squares = 0
            for cap in sorted(caps, reverse=True):
                used = min(left, cap)
                squares += used**2
                left -= used
            assert not left and squares >= mass * total / len(caps) - Fraction(max(caps)**2, 4)


if __name__ == "__main__":
    check_fill()
    for window in WINDOWS:
        verify(window)
        verify(window, with_third=True)
