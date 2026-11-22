"""Finite counting controls for the projective orbit-covering obstruction."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, isqrt, prod


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def projectivities(p):
    """Return all projective permutations with p denoting infinity."""
    inverses = [0] + [pow(i, -1, p) for i in range(1, p)]
    result = []
    for pivot in range(4):
        for tail in product(range(p), repeat=3-pivot):
            a, b, c, d = (0,)*pivot + (1,) + tail
            if (a*d - b*c) % p == 0:
                continue
            perm = []
            for z in range(p+1):
                num, den = (a, c) if z == p else (a*z+b, c*z+d)
                perm.append((num*inverses[den % p]) % p if den % p else p)
            result.append(tuple(perm))
    require(len(set(result)) == len(result) == p*(p*p-1), "wrong projective group")
    return result


def mask(points):
    return sum(1 << i for i in points)


def small_templates():
    # Include arbitrary pairs of nonidentity projectivities. In particular, the
    # three translates of a template can overlap and need not share a torus.
    p = 5
    group = projectivities(p)
    identity = tuple(range(p+1))
    triples = list(combinations(identity, 3))
    sets = [mask(x) for x in triples]
    domains = set()
    for x in triples:
        images = [mask(g[i] for i in x) for g in group if g != identity]
        domains.update(mask(x) | first | second for first, second in combinations(images, 2))
    for domain in domains:
        actual = Counter((s & domain).bit_count() for s in sets)
        size = domain.bit_count()
        for k in range(4):
            expected = comb(size, k)*comb(p+1-size, 3-k)
            require(actual[k] == expected, "hypergeometric intersection distribution")
            incidence = sum(comb(j, k)*freq for j, freq in actual.items())
            require(incidence == comb(size, k)*comb(p+1-k, 3-k), "subset first moment")
    require(len({d.bit_count() for d in domains}) >= 3, "overlap controls")
    return len(triples)*comb(len(group)-1, 2)


def small_arcs():
    # Enumerate actual labelled powers before identifying coincident arc sets.
    # An entire six-element set is captured iff it occurs as a distinct arc.
    p, length = 17, 6
    group = projectivities(p)
    arcs = Counter()
    for g in group:
        for start in range(p+1):
            point, support = start, 0
            for _ in range(length):
                support |= 1 << point
                point = g[point]
            arcs[support] += 1
    tested = captured = 0
    for sites in combinations(range(p+1), length):
        tested += 1
        captured += mask(sites) in arcs
    labelled = sum(freq*comb(support.bit_count(), length) for support, freq in arcs.items())
    require(0 < captured < tested == comb(p+1, length), "nonvacuous arc obstruction")
    require(captured <= labelled <= len(group)*(p+1), "labelled arc union bound")
    return captured, tested


def large_integer_controls():
    p = (1 << 61)-1
    population, s, length, k = p+1, 1 << 30, 1 << 20, 24
    # At this prime one uniform S of a billion sites avoids 24 hits in every
    # million-site projective arc with an explicitly bounded failure probability.
    union_bound = Fraction(population*p*(p*p-1)*comb(length, k)*comb(s, k),
                           comb(population, k))
    require(union_bound < Fraction(1, 1 << 96), "exact short-arc probability")

    def density(x, t):
        nominal = x*t
        # Rounding N^(-3/8) up to 2^(-22) preserves the upper bound.
        cutoff = (3*nominal+(1 << 22)-1)//(1 << 22) + 8*(x+3*t+8)
        require((3*s*nominal)**8*population <= (population*cutoff)**8,
                "single-template failure probability")
        return min(Fraction(1), Fraction(cutoff, nominal))

    comparisons = 0
    for powers in ((10, 17, 24, 26), (25, 27, 23, 24), (14, 13, 27, 24), (26, 15, 2, 35)):
        x, y, t, u = (1 << exponent for exponent in powers)
        demand = density(x, t)*density(y, u)
        m = min(x, y)
        for h in (p-1, p+1):
            eligible = 0
            for r in range(2, 33):
                # Using the largest possible R and rounding sqrt(p) down makes
                # the moment certificate more favorable to a proposed cover.
                numerator = (Fraction(h*prod(range(1, 2*r, 2)), m**(r-1))
                             + (2*r-2)*isqrt(p))
                relaxed = numerator/min(h, t*u)
                require(demand**r <= relaxed, "moment charge beat the trivial cost")
                eligible += relaxed < 1
                comparisons += 1
            require(eligible, "moment controls did not enter the nontrivial regime")
    return comparisons


if __name__ == "__main__":
    templates = small_templates()
    captured, tested = small_arcs()
    moments = large_integer_controls()
    print(f"{templates} mixed-template configurations; {captured}/{tested} six-site sets in one "
          f"arc over F_17; 61-bit arc failure < 2^-96; {moments} exact moment comparisons")
