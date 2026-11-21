#!/usr/bin/env python3
"""Check actual small-domain bad-scalar sets and the production power-fiber certificate."""
from itertools import combinations


def domain_vanisher(domain, p):
    coeffs = [1]
    for x in domain:
        product = [0] * (len(coeffs) + 1)
        for j, a in enumerate(coeffs):
            product[j] -= x * a
            product[j + 1] += a
        coeffs = [c % p for c in product]
    return coeffs


def evaluate(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def interpolation_weights(nodes, x, p):
    weights = []
    for y in nodes:
        num = den = 1
        for z in nodes:
            if z != y:
                num = num * (x - z) % p
                den = den * (y - z) % p
        weights.append(num * pow(den, -1, p) % p)
    return weights


def actual_bad_set(domain, rows, k, e, p):
    """On a witness set the first k sites force each interpolant.

    If a larger witness is bad, retain any k basis sites and one site of
    nonjointness. Extend within that witness to n-e sites. This preserves
    the folding agreement and nonjointness whenever n-e > k.
    """
    bad = set()
    for sites in combinations(domain, len(domain) - e):
        basis = sites[:k]
        candidate = None
        for x in sites[k:]:
            weights = interpolation_weights(basis, x, p)
            a, b = [(row[x] - sum(w * row[y] for w, y in zip(weights, basis))) % p
                    for row in rows]
            if b:
                t = -a * pow(b, -1, p) % p
                if candidate is not None and candidate != t:
                    break
                candidate = t
            elif a:
                break
        else:
            if candidate is not None:
                bad.add(candidate)
    return bad


def check_small(h, p):
    size = h + 1
    fibers = {}
    for x in range(1, p):
        fibers.setdefault(pow(x, size, p), []).append(x)
    groups = list(fibers.values())[:3]
    assert len(groups) == 3 and all(len(group) == size for group in groups)
    core = set().union(*groups)
    padding = [x for x in range(p) if x not in core][:4 * h - len(core)]
    domain = sorted(core.union(padding))
    vanisher = domain_vanisher(domain, p)
    rows = [{x: evaluate(poly, x, p) for x in domain}
            for poly in (vanisher[h:], [-a for a in vanisher[h + 1:]])]
    bad = actual_bad_set(domain, rows, 2 * h, h, p)
    assert bad == core, (p, sorted(bad), sorted(core))
    print(f"F_{p}, n={4*h}, k={2*h}, e={h}: {len(bad)} actual bad scalars")


def check_production():
    h = 2**28
    p = (h + 1) * 47939 * 2**114 + 1
    assert (h + 1) * 47939 < 2**114
    assert pow(3, (p - 1) // 2, p) == p - 1  # Proth's theorem
    assert (p - 1) % (h + 1) == (p - 1) % (4 * h) == 0
    assert len({pow(x, h + 1, p) for x in (1, 2, 4)}) == 3
    b = p // 2**128
    assert h + 2 <= b < 3 * (h + 1) <= 4 * h
    print(f"Production p={p}, budget={b}, sharp endpoint count={3*(h+1)}")


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Assertions must be enabled for this verifier.")
    check_small(3, 13)
    check_small(4, 31)
    check_production()
