#!/usr/bin/env python3
"""Classify six saturated, cropped lists with a common locator and a power map.

The candidate generator fixes two points in the coefficient plane. Slopes are
sixteenth roots. The splitting ansatz and reductions are justified in
docs/research/proximity-gap/saturated-list-pencils.md. Arithmetic is exact.
"""
from collections import Counter
from itertools import combinations, count

PRIMES = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)
FIBER_SIZE = 2**26
AGREEMENTS = 379625061


def certify(p):
    root = next(z for g in count(2) if pow(z := pow(g, (p-1)//16, p), 8, p) == p-1)
    roots = tuple(pow(root, i, p) for i in range(16))
    roots_set = set(roots)
    if len(roots_set) != 16:
        raise ArithmeticError("fiber labels are not distinct")

    def line(P, Q):
        x, y = P
        u, v = Q
        if x == u:
            return None
        slope = (v-y)*pow(u-x, -1, p) % p
        if slope not in roots_set:
            return None
        return slope, (y-slope*x) % p

    def extend(lines, more):
        result = lines.copy()
        for slope, intercept in more:
            if slope in result and result[slope] != intercept:
                return None
            result[slope] = intercept
        return result

    def crop_possible(points, lines):
        d = FIBER_SIZE
        c = d-1
        forced = [
            c + d*sum((y-s*x) % p == b for s, b in lines.items())
            for x, y in points
        ]
        free = 16*d - c - d*len(lines)
        return max(forced) <= AGREEMENTS and sum(AGREEMENTS-i for i in forced) <= free

    counts = Counter()

    def explore(points, pool, lines):
        counts[len(points)] += 1
        if len(points) == 6:
            if crop_possible(points, lines):
                raise ValueError(f"found a feasible cropped list over {p}: {points}")
            return
        for j, (Q, additions) in enumerate(pool):
            new_lines = extend(lines, additions)
            if new_lines is None:
                continue
            tail = []
            for T, previous in pool[j+1:]:
                extra = line(Q, T)
                if extra is not None:
                    tail.append((T, previous+(extra,)))
            explore(points+(Q,), tail, new_lines)

    off_axis = []
    for s in roots[1:]:
        for t in roots[1:]:
            if s != t:
                x = (1-t)*pow(s-t, -1, p) % p
                off_axis.append((x, s*x % p))
    for j, T in enumerate(off_axis):
        points = ((0, 0), (1, 1), T)
        x, y = T
        on_axis = []
        for s in roots[1:]:
            u = (y-s*x)*pow(1-s, -1, p) % p
            if u not in (0, 1):
                on_axis.append((u, u))
        lines = extend({}, [line(P, Q) for P, Q in combinations(points, 2)])
        pool = []
        for Q in off_axis[j+1:]+on_axis:
            additions = tuple(line(P, Q) for P in points)
            if None not in additions:
                pool.append((Q, additions))
        explore(points, pool, lines)
    if counts != {3: 210, 4: 7452, 5: 48220, 6: 122430}:
        raise ArithmeticError(f"unexpected tree sizes: {counts}")
    print(f"{p}: {counts[6]} compatible normalized six-point configurations, no cropped example")


if __name__ == "__main__":
    for prime in PRIMES:
        certify(prime)
