#!/usr/bin/env python3
"""Recover split fibers from one color and the holes using a critical resultant."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from itertools import combinations
from math import comb, gcd as integer_gcd, isqrt, prod


P1 = 2**30 * (2**128 + 192) + 1
P2 = 2**30 * (2**129 + 13) + 1


def check(result, context):
    if not result:
        raise ArithmeticError(context)


def clean(values, p):
    poly = [v % p for v in values]
    while poly and not poly[-1]:
        poly.pop()
    return tuple(poly)


def add(a, b, p, scale=1):
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, value in enumerate(b):
        out[i] += scale * value
    return clean(out, p)


def mul(a, b, p):
    if not a or not b:
        return ()
    out = [0] * (len(a) + len(b) - 1)
    for i, left in enumerate(a):
        for j, right in enumerate(b):
            out[i + j] += left * right
    return clean(out, p)


def derivative(a, p):
    return clean([i * a[i] for i in range(1, len(a))], p)


def euclidean(a, b, p):
    inv = pow(b[-1], -1, p)
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b):
        shift = len(a) - len(b)
        factor = a[-1] * inv % p
        q[shift] = factor
        a = add(a, (0,) * shift + b, p, -factor)
    return clean(q, p), a


def gcd(a, b, p):
    while b:
        a, b = b, euclidean(a, b, p)[1]
    return clean((v * pow(a[-1], -1, p) for v in a), p)


def resultant(a, b, p):
    factor = 1
    while len(b) > 1:
        m, n = len(a) - 1, len(b) - 1
        r = euclidean(a, b, p)[1]
        if not r:
            return 0
        sign = -1 if (m * n) % 2 else 1
        factor = factor * sign * pow(b[-1], m - len(r) + 1, p) % p
        a, b = b, r
    return factor * pow(b[0], len(a) - 1, p) % p


def val(a, x, p):
    value = 0
    for coeff in reversed(a):
        value = (x * value + coeff) % p
    return value


def interpolate(values, p):
    result = ()
    basis = (1,)
    for x, target in enumerate(values):
        coeff = (target - val(result, x, p)) * pow(val(basis, x, p), -1, p) % p
        result = add(result, basis, p, coeff)
        basis = mul(basis, (-x, 1), p)
    return result


def sqrt_mod(value, p):
    value %= p
    if value == 0:
        return 0
    if pow(value, (p - 1) // 2, p) != 1:
        return None
    odd, order = p - 1, 0
    while odd % 2 == 0:
        odd //= 2
        order += 1
    nonsquare = 2
    while pow(nonsquare, (p - 1) // 2, p) == 1:
        nonsquare += 1
    c, x, t = pow(nonsquare, odd, p), pow(value, (odd + 1) // 2, p), pow(value, odd, p)
    while t != 1:
        i, power = 0, t
        while power != 1:
            i += 1
            power = power * power % p
        b = pow(c, 2 ** (order - i - 1), p)
        order, c, x, t = i, b * b % p, x * b % p, t * b * b % p
    return x


def small_roots(poly, p):
    if len(poly) <= 1:
        return []
    if len(poly) == 2:
        return [-poly[0] * pow(poly[1], -1, p) % p]
    check(len(poly) == 3, "more than two high-multiplicity critical values")
    a, b, c = poly[2], poly[1], poly[0]
    s = sqrt_mod(b * b - 4 * a * c, p)
    if s is None:
        return []
    return sorted({(-b + sign * s) * pow(2 * a, -1, p) % p for sign in [-1, 1]})


def locator(roots, p, origin=0, reverse=False):
    poly = (1,)
    for root in roots:
        factor = (1, origin - root) if reverse else (origin - root, 1)
        poly = mul(poly, factor, p)
    return poly


def recover(fixed, rest, p):
    d = len(fixed)
    check(len(rest) == 2 * d and 0 < d and p > 3 * d - 2, "reconstruction parameters")
    # A fixed root at infinity leaves all unknown critical points in this affine chart.
    anchor = fixed[0]
    a = locator(fixed, p, anchor, reverse=True)
    f = locator(rest, p, anchor, reverse=True)
    a2 = mul(a, a, p)
    critical = add(mul(a, derivative(f, p), p), mul(derivative(a, p), f, p), p, -2)
    check(len(critical) == 3 * d - 1, "critical degree")
    samples = [resultant(critical, add(f, a2, p, -v), p) for v in range(3 * d - 1)]
    branch = interpolate(samples, p)
    check(len(branch) == len(critical), "branch polynomial degree")
    heavy = branch
    part = branch
    for _ in range(1, d):
        part = derivative(part, p)
        heavy = gcd(heavy, part, p)
    candidates = euclidean(heavy, gcd(heavy, derivative(heavy, p), p), p)[0]
    # A point of the uncolored union supplies the sign of the square root.
    anchor = rest[0]
    a = locator(fixed, p, anchor)
    f = locator(rest, p, anchor)
    a2 = mul(a, a, p)
    out = []
    for v in small_roots(candidates, p):
        if not v:
            continue
        target = add(a2, f, p, -pow(v, -1, p))
        w = [a[0]]
        inv = pow(2 * w[0], -1, p)
        for i in range(1, d + 1):
            cross = sum(w[j] * w[i-j] for j in range(1, i))
            w.append(((target[i] if i < len(target) else 0) - cross) * inv % p)
        if mul(w, w, p) != target:
            continue
        minus = add(a, w, p, -1)
        left = tuple(x for x in sorted(rest) if val(minus, x - anchor, p) == 0)
        right = tuple(sorted(set(rest) - set(left)))
        check(len(left) == len(right) == d, "incomplete roots after square test")
        out.append(tuple(sorted([left, right])))
    return sorted(out)


def subgroup(p, n, seed):
    generator = pow(seed, (p - 1) // n, p)
    check(pow(generator, n, p) == 1 and pow(generator, n // 2, p) != 1, "grid order")
    return [pow(generator, i, p) for i in range(n)]


def check_symmetries(fixed, rest, solutions, grid, p):
    z, u = set(fixed), set(rest)
    size = len(solutions)
    if {-x % p for x in z} == z and {-x % p for x in u} == u:
        descended = 0
        for left, right in solutions:
            negated = {-x % p for x in left}
            if negated == set(left):
                descended += 1
            else:
                check(negated == set(right), "half-turn does not preserve this completion")
                check(prod(rest) % p == prod(fixed)**2 % p, "unequal products for odd square root")
        check(len(fixed) % 4 != 2 or descended <= 1, "two odd-degree descended completions")
    for b in grid:
        fixed_points = {x for x in grid if x*x % p == b}
        if len(fixed_points) != 2 or not fixed_points.issubset(u):
            continue
        if {b*pow(x, -1, p) % p for x in z} != z or {b*pow(x, -1, p) % p for x in u} != u:
            continue
        check(size == 2, "reflection failed to produce its second completion")
        check((prod(rest) + prod(fixed)**2) % p == 0, "reflection product")


def census(p, grid, d, verify_every):
    # Independent enumeration using collinearity of monic locator coefficient vectors.
    psets = {roots: locator(roots, p) for roots in combinations(sorted(grid), d)}
    remaining = set(psets)
    counts = Counter()
    verified = 0
    while remaining:
        fixed = min(remaining)
        orbit = {tuple(sorted(z*x % p for x in fixed)) for z in grid}
        remaining.difference_update(orbit)
        groups = defaultdict(list)
        available = sorted(set(grid) - set(fixed))
        for roots in combinations(available, d):
            delta = add(psets[roots], psets[fixed], p, -1)
            inv = pow(delta[-1], -1, p)
            groups[tuple(t * inv % p for t in delta)].append(roots)
        partitions = defaultdict(list)
        for group in groups.values():
            for left, right in combinations(group, 2):
                rest = tuple(sorted(left + right))
                check(len(set(rest)) == len(rest), "pencil members share a root")
                partitions[rest].append(tuple(sorted([left, right])))
        local = Counter(map(len, partitions.values()))
        local[0] = comb(len(available), 2*d) - len(partitions)
        for multiplicity, amount in local.items():
            counts[multiplicity] += len(orbit) * amount
            check(not amount or multiplicity <= (1 if d % 2 else 2), "uniqueness bound")
        for rest, solutions in partitions.items():
            check_symmetries(fixed, rest, solutions, grid, p)
            if len(solutions) == 2:
                check(all(len(set(x) & set(y)) == d // 2 for x in solutions[0]
                          for y in solutions[1]), "cross-intersection size")
        seen = Counter()
        for rest in combinations(available, 2*d):
            direct = partitions.get(rest, [])
            if verify_every or seen[len(direct)] < 3:
                check(recover(fixed, rest, p) == sorted(direct), (p, fixed, rest))
                verified += 1
                seen[len(direct)] += 1
    return counts, verified


def check_elliptic_trace():
    p = P1
    q = 52447244997910193717739548112237131
    middle = 2761401159115516212413
    # Pocklington's sufficient known prime factors use base two at both levels.
    certified = {412971703, 24001}
    for small in certified:
        check(all(small % i for i in range(2, isqrt(small) + 1)), small)
    for n, factors in [(middle, (412971703, 24001)), (q, (middle,))]:
        product = prod(factors)
        check(set(factors) <= certified and (n-1) % product == 0 and product**2 > n, n)
        check(pow(2, n-1, n) == 1, n)
        for factor in factors:
            check(integer_gcd(pow(2, (n-1)//factor, n)-1, n) == 1, (n, factor))
        certified.add(n)

    def plus(left, right):
        if left is None:
            return right
        if right is None:
            return left
        x, y = left
        z, w = right
        if x == z and (y+w) % p == 0:
            return None
        if x == z:
            slope = (3*x*x-8*x+2)*pow(2*y, -1, p) % p
        else:
            slope = (y-w)*pow(x-z, -1, p) % p
        u = (slope*slope+4-x-z) % p
        return u, (slope*(x-u)-y) % p

    def times(n, point):
        out = None
        while n:
            if n % 2:
                out = plus(out, point)
            point = plus(point, point)
            n //= 2
        return out

    trace = 1201616412679574549121762
    order = p+1-trace
    x, y = 1, 125829621549097067457234094028236226857884909488
    check((y*y - (x**3-4*x*x+2*x)) % p == 0, "point on elliptic quotient")
    check(16*p < q*q and trace*trace <= 4*p and order % q == 0, "Hasse interval")
    check(times(order, (x, y)) is None and times(order//q, (x, y)) is not None,
          "elliptic order certificate")
    # Count both explicit quotient models on all nonsingular members at a small prime.
    for a in range(17):
        if (a*a-4) % 17 == 0:
            continue
        for twist in (1, 3):
            def character(value):
                value = pow(twist*value % 17, 8, 17)
                return -1 if value == 16 else value
            genus_two = sum(character(u**5+a*u**3+u) for u in range(17))
            plus_curve = sum(character((v*v+a-2)*(v+2)) for v in range(17))
            minus_curve = sum(character((v*v+a-2)*(v-2)) for v in range(17))
            check(genus_two == 2*plus_curve == 2*minus_curve, (a, twist))
    print(f"Certified the first-prime untwisted elliptic trace {trace}.")


def check_cartier_pullbacks():
    p, a, i = 17, 3, 4
    # s=(X-a)/(aX-1) interchanges inversion on both lines. Neither 0 nor
    # infinity lies over a branch target. Replacing X by X^e yields a smooth
    # curve even when some preimages require an extension of F17.
    branch = [(a-v)*pow(1-a*v, -1, p) % p for v in (0, 1, -1, i, -i)]
    branch.append(pow(a, -1, p))
    check(len(set(branch)) == 6 and 0 not in branch and i*i % p == p-1, "six fibers")
    trace = -sum({0: 0, 1: 1, 16: -1}[pow(x*(x*x-4*x+2) % p, 8, p)] for x in range(p))

    def nullity(rows):
        rows = [row.copy() for row in rows]
        rank = 0
        for j in range(len(rows)):
            pivot = next((r for r in range(rank, len(rows)) if rows[r][j] % p), None)
            if pivot is None:
                continue
            rows[pivot], rows[rank] = rows[rank], rows[pivot]
            inv = pow(rows[rank][j], -1, p)
            for r in range(rank+1, len(rows)):
                factor = rows[r][j] * inv % p
                rows[r] = [(x-factor*y) % p for x, y in zip(rows[r], rows[rank])]
            rank += 1
        return len(rows) - rank

    dimensions = []
    for degree in (1, 2, 3):
        polynomial = (1,)
        for x in branch:
            polynomial = mul(polynomial, (-x,) + (0,)*(degree-1) + (1,), p)
        power = (1,)
        for _ in range((p-1)//2):
            power = mul(power, polynomial, p)
        g = 3*degree - 1
        def coeff(k):
            return power[k] if 0 <= k < len(power) else 0
        ranks = [nullity([[(coeff(p*r-j) - (t if r == j else 0)) % p
                           for j in range(1, g+1)] for r in range(1, g+1)])
                 for t in (trace, -trace)]
        check(max(ranks) >= 2, ("elliptic Cartier eigenspace", degree, ranks))
        dimensions.append(tuple(ranks))
    print(f"Cartier kernel dimensions for degrees 1, 2, 3 at F17: {dimensions}")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="also run the critical resultant on every cubic orbit representative")
    full = parser.parse_args().full
    check_elliptic_trace()
    check_cartier_pullbacks()
    for p, seed in [(17, 3), (P1, 3), (P2, 37)]:
        grid = subgroup(p, 16, seed)
        for n, d in ([(8, 2), (16, 2), (16, 3)] if p == 17 else [(16, 2), (16, 3)]):
            counts, verified = census(p, grid[::16//n], d, full or d <= 2)
            check(sum(counts.values()) == comb(n, d)*comb(n-d, 2*d), "coverage")
            field = "F17" if p == 17 else ("p1" if p == P1 else "p2")
            print(f"{field}, n={n}, d={d}: {dict(sorted(counts.items()))}; "
                  f"{verified} resultant reconstructions")
        fixed = (grid[0], grid[8])
        rest = tuple(grid[i] for i in (1, 15, 2, 14))
        check(len(recover(fixed, rest, p)) == 2, "sharp production lift")


if __name__ == "__main__":
    main()
