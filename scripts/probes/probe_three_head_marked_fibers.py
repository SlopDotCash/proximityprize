#!/usr/bin/env python3
"""Check marked-fiber attack sizes and reconstruct a 72-label witness on 34 field sites."""
from itertools import combinations, count

from probe_four_head_extension_sharpness import heads
from probe_quarter_slope_reconstruction import MAPS, P, double_sites, interpolate


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def fold_label(source, target):
    a, b = source
    u, v = target
    return (u-a)*pow((b-v) % P, -1, P) % P


def verify_small():
    owners, old_labels = {}, set()
    outside = set()

    def fresh(x, own):
        values = heads(x)
        word = values[own[0]]
        matches = tuple(i for i, point in enumerate(values) if point == word)
        require(matches == own, "unintended joint incidence")
        return [fold_label(values[i], word) for i in range(1, 4) if i not in own]

    def add(x, own, available):
        require(x not in owners and len(available) == len(set(available)), "site collision")
        require(old_labels.isdisjoint(available) and outside.isdisjoint(available), "label collision")
        owners[x] = own
        old_labels.update(available)

    for j, k in combinations(range(3), 2):
        for sign, own in ((1, (0, 4-j-k)), (-1, (j+1, k+1))):
            for x in double_sites(j, k, sign):
                add(x, own, fresh(x, own))

    # A marked input on edge (0,i) is the inverse image of gamma under a degree-one map.
    for gamma in count(2):
        if gamma in old_labels:
            continue
        proposed = []
        for i, (a, b, c, d) in enumerate(MAPS, 1):
            den = ((gamma-1)*c-(gamma+1)*a) % P
            if den == 0:
                break
            x = ((gamma+1)*b-(gamma-1)*d)*pow(den, -1, P) % P
            if x in owners or len(set(heads(x))) < 4:
                break
            directions = fresh(x, (i,))
            proposed.append((x, i, directions))
        if len(proposed) != 3 or len({x for x, _, _ in proposed}) != 3:
            continue
        labels = [z for _, _, zs in proposed for z in zs]
        if (len(set(labels)) != 6 or gamma in labels or
                set(labels) & (old_labels | outside)):
            continue
        outside.add(gamma)
        for x, i, directions in proposed:
            require(fold_label(heads(x)[0], heads(x)[i]) == gamma, "incorrect marked fiber")
            add(x, (i,), directions)
        if len(outside) == 6:
            break

    for x in count(1):
        if x in owners or len(set(heads(x))) < 4 or len({b for a, b in heads(x)}) != 4:
            continue
        directions = fresh(x, (0,))
        if len(set(directions)) == 3 and set(directions).isdisjoint(old_labels | outside):
            add(x, (0,), directions)
        if len(owners) == 34:
            break

    words = {x: heads(x)[own[0]] for x, own in owners.items()}
    labels = set()
    for i in range(4):
        core = [x for x, own in owners.items() if i in own]
        require(len(core) == (10 if i == 0 else 12), "joint core size")
        fixed = core[:4]
        available = outside if i == 0 else {
            fold_label(heads(x)[i], words[x]) for x in owners if x not in core}
        require(labels.isdisjoint(available), "assigned label repeated")
        labels.update(available)
        for z in available:
            folded = [(words[x][0]+z*words[x][1]) % P for x in fixed]
            support = [x for x in owners
                       if interpolate(fixed, folded, x) == (words[x][0]+z*words[x][1]) % P]
            require(len(support) >= 13 and set(core) <= set(support), "insufficient agreements")
            require(any(tuple(interpolate(fixed, [words[y][r] for y in fixed], x)
                              for r in range(2)) != words[x] for x in support),
                    "joint explanation on chosen support")
    require(len(labels) == 72 and len(old_labels) == 66, "literal MCA count")
    return len(labels), sorted(outside)


def verify_production():
    n = 2**30
    for e, d, m in ((715827881,71582789,8), (715827880,71582790,8),
                    (715827879,71582792,9), (715827878,76695849,12),
                    (715827877,79536437,15)):
        t, c = n-e, n-e-1
        h, h4 = c-2*d, n-3*c+2*d
        demand = t-2*d-h4
        degrees = [(d+j)//3 for j in range(3)]
        require(min(degrees) > 0 and sum(degrees) == d and h4 >= 0, "quartet degrees")
        require(m*demand <= sum(min(h,m*r) for r in degrees) and 1 <= demand,
                "marked agreement schedule")
        require(4*d+3*h+h4 == n and c >= d+1 and 2*d+h4 >= d+1, "domain and uniqueness")
        mass = 3*(e+1)+m
        require(mass > 2*n, "integer budget")
        print(f"conditional generic schedule k={d+1} e={e} marked={m} count={mass}")


if __name__ == "__main__":
    verify_production()
    size, marked = verify_small()
    print(f"named prime, 34 chosen sites, dimension 4, 21 errors: {size} actual bad labels; marks {marked}")
