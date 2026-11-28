#!/usr/bin/env python3
"""Verify the quarter-rate outsider bounds and local charges."""
from itertools import combinations, product
from math import comb


def production():
    n = 2**30
    d = n // 4 - 1
    end = 480_946_858
    t = n - end
    for v in range(7):
        assert comb(v, 2) >= 3 * v - 6
        assert comb(v, 2) >= 2 * v - 3
    # Pair roots, with -1, 0, +1 the coefficients of direction degree.
    for outsiders, weight in ((2, -2), (3, 0)):
        weights = [int(i >= 3) + int(j >= 3) - 1
                   for i, j in combinations(range(3 + outsiders), 2)]
        assert sum(weights) == weight
    hole_direction_cap = (6*d - 6*(t-1) + 2*n + 2046) // 6
    three_floor = 6*t - 3 - 2*n - 5*d
    assert (hole_direction_cap, three_floor) == (33_554_772, 67_108_870)
    assert t - hole_direction_cap - 1 > d
    assert n - 3*d > hole_direction_cap
    last_one_class = n - (33*d + 10*n + 1044 - 9)//33 - 1
    assert last_one_class == 479_930_027
    dir_cap_two = (33*d + 10*n + 1044 - 33*t)//9
    triple_floor_two = 2*(10*t - 6 - 3*n - 10*d + 2)
    assert (dir_cap_two, triple_floor_two) == (3_728_380, 44_739_268)
    for e, feasible in ((472_957_708, False), (472_957_709, True)):
        t1 = n - e
        r = max(0, 5*t1 - 2*n - 3*d - 3)
        r += r % 2
        x = 3*(t1-1) - n - 3*r//2
        assert (x+3*r <= 3*(d-1)) == feasible
    print("production", hole_direction_cap, three_floor, last_one_class,
          dir_cap_two, triple_floor_two)


def site_charge_control():
    for heads in product(range(3), repeat=3):
        values = len(set(heads))
        charge = {1: 6, 2: 5, 3: 3}[values]
        for received in range(4):
            joint = sum(f == received for f in heads)
            fresh = int(any(f != received for f in heads))
            assert charge >= 2*joint+fresh
            if not joint:
                assert charge-fresh >= 2
    n = 2**30
    d = n//4 - 1
    t = n - 480_946_858
    assert 10*t - 6 - 3*n - 10*d + 4 == 22_369_636
    assert (4*n-3*(d-1)) % 6 == 4
    assert [(4-a) % 6 for a in (0, 1)] == [4, 3]
    print("repeated outsider exclusion", 22_369_636, "line-hole cap", 2046//2)


if __name__ == "__main__":
    production()
    site_charge_control()
