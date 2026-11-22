#!/usr/bin/env python3
"""Check the greedy half-rate interpolation and anchored tangent allocation."""
from dataclasses import dataclass
from math import comb

from probe_tangent_head_windows import BUDGET, N

ERRORS = 310_285_000
D = N // 2 - 1
T = N - ERRORS
CORE = T - 255
HEAD_CUTOFF = ERRORS // 256 + 1
CAP = 2_101_754_336


@dataclass(frozen=True)
class Shape:
    order: int
    degree: int
    scalar: int
    drop: int

    def weight(self, p):
        return self.order * T - p * self.drop * D

    def surplus(self, p):
        def jets(r):
            return sum((r - j) * (self.scalar + 1 - j) for j in range(r))

        weight = self.weight(p)
        columns = sum((self.scalar + 1 - j) * max(0, weight - j * D)
                      for j in range(self.degree + 1))
        saving = jets(self.order) - jets(self.order - self.drop)
        correction = self.drop**2 * (self.scalar + 1)
        for owners in range(p + 1):
            check(self.order >= owners * self.drop, 'site order')
            check(jets(self.order - owners * self.drop) + owners * saving <=
                  jets(self.order) + comb(owners, 2) * correction, 'local row estimate')
        rows = N * jets(self.order) - p * CORE * saving + comb(p, 2) * D * correction
        return columns - rows


PRIMARY = tuple(Shape(26, 36-p, scalar, int(p > 0))
                for p, scalar in enumerate((227608, 209858, 195264, 183748, 175231, 169633, 166876)))
COMPANION = tuple(Shape(*row) for row in (
    (51, 72, 1355, 0), (51, 70, 1284, 2), (51, 68, 1229, 2), (53, 69, 1190, 2),
    (49, 65, 1164, 1), (49, 64, 1128, 1), (46, 59, 1097, 1)))


def check(condition, what):
    if not condition:
        raise ValueError(what)


def head_mass(j):
    if j < 3:
        return j * (ERRORS + 1)
    denominator = CORE + (j - 1) * D
    union = (j * CORE**2 + denominator - 1) // denominator
    return min(j * (ERRORS + 1), j * N - (j - 1) * union)


def tangent_cap(b, m, weight, degree, slope, anchors):
    ax = (2*b - 2)*weight - b*(b-1)*D
    gz = (2*b - 2)*m - b*(b-1)
    height = 2*ax*gz + 2*weight*m
    loss = (gz+m)*N
    h = comb(degree + 2, 2)
    gap = (slope*h*T - comb(slope+2, 3)*N -
           degree*(degree+1)*(degree+2)//3*D - slope*anchors*255)
    check(gap > 0 and ax >= 0 and gz >= 0, 'tangent hypotheses')
    return (gz + 2*b*m + degree*m*(m-1) +
            (h-anchors)*(slope*loss+degree*height)//gap)


def run():
    check(HEAD_CUTOFF > PRIMARY[0].scalar and 3*CORE > N + 2*D, 'greedy hypotheses')
    maxima = []
    for p, (primary, companion) in enumerate(zip(PRIMARY, COMPANION)):
        slack = (primary.surplus(p), companion.surplus(p))
        check(min(slack) > 0, 'both nonzero surfaces')
        cutoff = max(HEAD_CUTOFF, primary.scalar*companion.degree +
                     primary.degree*companion.scalar + 1)
        m = companion.scalar
        check(T - m*N//cutoff - 3*(m*N//(cutoff-m)) > D, 'value-linear factors')
        head = max(head_mass(j) for j in range(PRIMARY[0].degree + 1) if min(j, 6) == p)
        worst = (head + primary.scalar, (0, 0))
        exact = worst[0]
        for total in range(1, primary.degree + 1):
            prices = [0, cutoff]
            for b in range(2, total + 1):
                weight = primary.weight(p) - 1 - (total-b)*D
                check(weight >= b*D and b <= companion.degree and b <= 240 < m,
                      'component degrees')
                if p:
                    price = tangent_cap(b, m, weight, 1, 1, min(p, 2))
                else:
                    price = max(tangent_cap(b, 240, weight, 1, 1, 0),
                                tangent_cap(b, m, weight, 16, 14, 0))
                prices.append(max(cutoff, price))
            for b in range(1, total + 1):
                worst = max(worst, (head + primary.scalar + total*prices[b]//b, (total, b)))
            # A second check uses the exact integer partition recurrence.
            best = [0]
            for x in range(1, total + 1):
                best.append(max(best[x-b] + prices[b] for b in range(1, x+1)))
            exact = max(exact, head + primary.scalar + best[total])
        check(exact <= worst[0] <= BUDGET, 'all partitions')
        maxima.append(worst[0])
        print(f'p={p} surpluses={slack} cutoff={cutoff} labels={worst[0]} '
              f'at total degree and part {worst[1]}')
    check(max(maxima) == CAP, 'maximum')
    print(f'At most {CAP} labels at {ERRORS} errors, {BUDGET-CAP} below budget.')


if __name__ == '__main__':
    run()
