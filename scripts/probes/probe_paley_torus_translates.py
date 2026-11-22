"""Exact projective Paley walk checks on split and nonsplit tori over small primes."""
from collections import Counter
from itertools import product
from math import prod

from probe_paley_translate_moments import trace_power


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def check_torus(p, delta, orders):
    points = [(z, 1) for z in range(p)] + [(1, 0)]
    infinity = (1, 0)
    character = [0] + [1 if pow(z, (p-1)//2, p) == 1 else -1 for z in range(1, p)]

    def det(x, y):
        return (x[0]*y[1] - x[1]*y[0]) % p

    def line(v):
        x, y = v
        require(x % p or y % p, "projective zero")
        return (x*pow(y, -1, p) % p, 1) if y % p else infinity

    def apply(g, x):
        a, b = g
        return ((a*x[0]+delta*b*x[1]) % p, (b*x[0]+a*x[1]) % p)

    singular = [g for g in points if not (g[0]**2-delta*g[1]**2) % p]
    group = [g for g in points if g not in singular]
    orbit = {line(apply(g, infinity)) for g in group}
    action = {(g, x): line(apply(g, x)) for g in group for x in orbit}
    require(len(singular) == (2 if character[delta] == 1 else 0) and
            len(orbit) == len(group) == p+1-len(singular), "regular orbit size")
    group_label = {(action[g, y], y): g for g in group for y in orbit}
    require(len(group_label) == len(orbit)**2, "unique group label at every edge")

    # The identity parameter and a vertex are both at infinity. Some finite group
    # parameters also send a finite vertex through the pole of the affine chart.
    require(any(x != infinity and g != infinity and action[g, x] == infinity
                for g in group for x in orbit), "affine pole not exercised")
    finite = sorted(orbit - {infinity})
    xs, ys = (infinity, finite[0], finite[1]), (finite[-1], infinity, finite[-2])
    if p != 5:
        ys += (finite[0],)
    # The rectangle at infinity and zero supplies an even-label square with
    # negative sign in the nonsplit case, and positive sign in the split case.
    zero = (0, 1)
    corners = tuple(product((infinity, zero), repeat=2))
    require(sorted(Counter(group_label[e] for e in corners).values()) == [2, 2],
            "involution rectangle labels")
    for g in group:
        if all(g):
            sign = prod(character[det(x, action[g, y])] for x, y in corners)
            require(sign == character[delta], "involution rectangle phase")
    edges = list(product(xs, ys))
    labels, coefficients, entries = {}, {}, {}
    for x, y in edges:
        a, b = det(x, y), det(x, apply((0, 1), y))
        root = line((-b, a))
        require(root == group_label[x, y] and root not in singular, "wrong linear-factor root")
        labels[x, y] = root
        coefficients[x, y] = a if root != infinity else -b % p
        entries[x, y] = {g: character[det(x, action[g, y])] for g in group}
        for g in points:
            raw = det(x, apply(g, y))
            require(raw == coefficients[x, y]*det(g, root) % p, "linear factor normalization")
            if g not in singular:
                v = apply(g, y)
                scale = v[1] if v[1] else v[0]
                require(character[raw] == character[scale]*entries[x, y][g], "column sign")

    # The scalar changes of the chosen representatives factor by vertex, including
    # after moving both sides of a block back by the inverse of the row translation.
    left, right = group[:2], [infinity, *group[:2]]
    relative = Counter()
    for g, h in product(left, right):
        k = line(apply((g[0], -g[1]), h))
        relative[k] += 1
        for x in xs:
            for y in ys:
                require(action[g, action[k, y]] == action[h, y], "incorrect relative shift")
        require(all(character[det(action[g, x], action[h, y])] *
                    character[det(action[g, a], action[h, b])] *
                    character[det(action[g, x], action[h, b])] *
                    character[det(action[g, a], action[h, y])] ==
                    entries[x, y][k]*entries[a, b][k]*entries[x, b][k]*entries[a, y][k]
                    for x, a in product(xs, repeat=2) for y, b in product(ys, repeat=2)),
                "four-cycle changed under simultaneous projectivity")
    rows = sorted({action[g, x] for g in left for x in xs})
    cols = sorted({action[h, y] for h in right for y in ys})
    signed_sum = sum((-1)**(i+j+j//3)*character[det(x, y)]
                     for i, x in enumerate(rows) for j, y in enumerate(cols))
    walk_count = 0
    saw_odd_infinity = saw_even_only = saw_negative_factor = False
    for r in orders:
        traces = {g: 0 for g in group}
        paired = 0
        for xwalk in product(xs, repeat=r):
            for ywalk in product(ys, repeat=r):
                walk = [(xwalk[(i+j) % r], ywalk[i]) for i in range(r) for j in (0, 1)]
                mult = Counter(labels[edge] for edge in walk)
                odd = [z for z, m in mult.items() if m % 2]
                even_only = [z for z, m in mult.items() if not m % 2]
                c = character[prod(coefficients[e] for e in walk) % p]
                saw_negative_factor |= c == -1
                saw_odd_infinity |= infinity in odd
                saw_even_only |= bool(odd and even_only)
                # A binary form of even degree has an intrinsic quadratic sign on P^1.
                squarefree = {g: c*prod(character[det(g, z)] for z in odd) for g in points}
                raw = {g: squarefree[g] if g not in even_only else 0 for g in points}
                require(all(raw[g] == 1 for g in singular), "rank-one singular term")
                for g in group:
                    actual = prod(entries[edge][g] for edge in walk)
                    require(actual == raw[g], "uncancelled projective sign in an even walk")
                    traces[g] += actual
                total = sum(raw[g] for g in group)
                if odd:
                    require(len(odd) % 2 == 0 and
                            sum(squarefree.values())**2 <= (len(odd)-2)**2*p, "projective Weil bound")
                    require(total == sum(squarefree.values())-sum(squarefree[z] for z in even_only)
                            -len(singular), "projective root/pole correction")
                else:
                    paired += 1
                    require(total == c*(len(group)-len(mult)), "paired root count")
                walk_count += 1
        require(paired <= prod(range(1, 2*r, 2))*min(len(xs), len(ys))*max(len(xs), len(ys))**r,
                "unbalanced pairing bound")
        for g in group:
            matrix = [[entries[x, y][g] for y in ys] for x in xs]
            require(traces[g] == trace_power(matrix, r), "walk expansion versus Gram trace")
        tu = len(left)*len(right)
        require(signed_sum**(2*r)*tu**2 <= (len(rows)*len(cols)*tu)**r *
                sum(m*m for m in relative.values())*sum(traces.values()), "spread/compression bound")
    require(saw_odd_infinity and saw_even_only, "incomplete projective root controls")
    return walk_count, saw_negative_factor


def main():
    walks = cases = negatives = 0
    for p in (5, 7, 11, 13, 17):
        nonsquare = next(i for i in range(2, p) if pow(i, (p-1)//2, p) == p-1)
        for delta in (1, nonsquare):
            count, negative = check_torus(p, delta, (2, 3))
            walks += count
            cases += 1
            negatives += negative
    require(negatives > 0, "projective factor signs not exercised")
    print(f"{cases} regular tori, {walks} closed walks, all group parameters, both singular split matrices")


if __name__ == "__main__":
    main()
