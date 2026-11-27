"""Test involution-equivariant septic tetrahedron quotients on the named second prime."""

from collections import Counter
from itertools import combinations, product
from math import prod

from probe_smooth_four_head_attack import PRIME


def quotient(a, b, p):
    return a * pow(b % p, -1, p) % p


def primitive_root(order, p):
    divisors = []
    remaining = order
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            divisors.append(prime)
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        divisors.append(remaining)
    for seed in range(2, p):
        w = pow(seed, (p - 1) // order, p)
        if pow(w, order, p) == 1 and all(pow(w, order // l, p) != 1
                                         for l in divisors):
            return w
    raise ValueError("missing root of required order")


def ratios(roots, points, p):
    """Values of the monic locator ratio L(y)/L(-y), away from its divisors."""
    return [quotient(prod((y - a) % p for a in roots),
                     prod((-y - a) % p for a in roots), p) for y in points]


def candidate_roots(points, values, p):
    """Recover every finite nonzero lambda making three positive representatives equal."""
    pairs = {}
    for i, j in combinations(range(len(points)), 2):
        hi, hj = values[i], values[j]
        if hi != hj:
            b = quotient((hi + hj) * (points[j] - points[i]), hi - hj, p)
            pairs[i, j] = (b, -points[i] * points[j] % p)
    result = set()
    for i, j, k in combinations(range(len(points)), 3):
        if (i, j) not in pairs or (i, k) not in pairs:
            continue
        b, c = pairs[i, j]
        other_b, other_c = pairs[i, k]
        den = (b - other_b) % p
        num = (other_c - c) % p
        if den and (num * num + b * num * den + c * den * den) % p == 0:
            result.add(quotient(num, den, p))
    return result


def profile(roots, lam, nodes, p):
    """Count actual rational values by direct polynomial evaluation on the entire board."""
    if not lam or -lam % p in roots:
        return ()
    roots = [*roots, lam]
    sizes = Counter()
    for y in nodes:
        if y is None:
            sizes[p - 1] += 1
            continue
        a = prod((y - x) % p for x in roots) % p
        b = prod((-y - x) % p for x in roots) % p
        assert a or b
        sizes[quotient(a, b, p) if b else None] += 1
    return tuple(sorted(sizes.values(), reverse=True)[:4])


def control():
    # y^7 on mu_42 in F_337 gives six completely split seven-site fibers.
    p = 337
    w = primitive_root(42, p)
    nodes = [pow(w, j, p) for j in range(42)]
    zero_fiber = nodes[::6]
    roots, expected = zero_fiber[:6], zero_fiber[6]
    points = [x for x in nodes[:21] if x not in roots and -x % p not in roots]
    assert expected in candidate_roots(points, ratios(roots, points, p), p)
    assert profile(roots, expected, nodes, p) == (7, 7, 7, 7)

    # Independently enumerate every lambda for the same three-way equalities on F_97.
    p = 97
    w = primitive_root(32, p)
    nodes = [pow(w, j, p) for j in range(32)]
    for ix in ((0, 1, 2, 3, 4, 5), (1, 4, 7, 12, 18, 26), (0, 7, 9, 10, 20, 21)):
        roots = [nodes[i] for i in ix]
        points = [x for x in nodes[:16] if x not in roots and -x % p not in roots]
        h = ratios(roots, points, p)
        found = candidate_roots(points, h, p)
        expected = set()
        for lam in range(1, p):
            vals = [quotient(v * (lam - x), lam + x, p)
                    for x, v in zip(points, h) if (lam + x) % p]
            if max(Counter(vals).values()) >= 3:
                expected.add(lam)
        assert found == expected


def census(symmetry):
    p = PRIME
    z = primitive_root(64, p)
    board = [pow(z, 2 * i, p) for i in range(32)]
    if symmetry == "half turn":
        nodes = board
        partner = [(i + 16) % 32 for i in range(32)]
        motions = [(a, sign) for a in range(32) for sign in (1, -1)]
    else:
        exponent = 0 if symmetry == "vertex reflection" else 1
        u = pow(z, exponent, p)
        nodes = [quotient(x - u, x + u, p) if (x + u) % p else None for x in board]
        partner = [(exponent - i) % 32 for i in range(32)]
        motions = [(0, 1), (16, 1), (exponent, -1), (16 + exponent, -1)]
    pairs = [(i, j) for i, j in enumerate(partner) if i < j]
    assert all((nodes[i] + nodes[j]) % p == 0 for i, j in pairs)
    orbits = 0
    covered = set()
    profiles = Counter()
    for indices in combinations(range(len(pairs)), 6):
        points = [nodes[i] for j, (i, _) in enumerate(pairs) if j not in indices]
        for sites in product(*(pairs[j] for j in indices)):
            mask = sum(1 << i for i in sites)
            if mask in covered:
                continue
            orbits += 1
            for a, sign in motions:
                covered.add(sum(1 << ((a + sign * i) % 32) for i in sites))
            roots = [nodes[i] for i in sites]
            for lam in candidate_roots(points, ratios(roots, points, p), p):
                sizes = profile(roots, lam, nodes, p)
                if len(sizes) >= 3 and sizes[2] >= 6:
                    profiles[sizes] += 1
    return orbits, dict(sorted(profiles.items()))


def main():
    control()
    for symmetry, expected in [("half turn", 8190), ("vertex reflection", 80220),
                               ("edge reflection", 128352)]:
        orbits, profiles = census(symmetry)
        assert orbits == expected
        assert not profiles
        print(f"{symmetry}: {orbits} support orbits, candidate profiles {profiles}", flush=True)


if __name__ == "__main__":
    main()
