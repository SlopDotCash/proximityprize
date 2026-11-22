#!/usr/bin/env python3
"""Check translate membership and Wronskian multiplicities at prescribed small domains."""

from itertools import combinations
from math import comb, prod

from sw1_f3_union_rank import nullspace, rref


def captured(prime, sites, basis, errors):
    """All labels agreeing, after deletion of at most errors sites, with the row span."""
    words = [[pow((a + b) % prime, (prime - 1) // 2, prime) for a in sites]
             for b in range(prime)]
    found = set()
    for kept in combinations(range(len(sites)), len(sites) - errors):
        checks = nullspace([[row[i] for i in kept] for row in basis], len(kept), prime)
        for b, row in enumerate(words):
            if all(sum(c * row[i] for c, i in zip(check, kept)) % prime == 0 for check in checks):
                found.add(b)
    return found


def exact_cap(prime, size, dimension, unmasked):
    d = (prime - 1) // 2
    r = size - dimension
    return (d - dimension if unmasked else d + r - 1) // r


def check_wronskian(prime, sites, k, weights, extra, errors, width, labels):
    m = len(sites)
    unmasked = all(v == 1 for v in weights) and not extra
    length = (m - k - width + 1) // (len(extra) + 1)
    if width <= errors or length <= errors:
        return False
    d = (prime - 1) // 2
    degree = d + length - 1
    qdim = m - k - length + 1
    dual = [pow(v * prod(a - t for t in sites if t != a), -1, prime)
            for a, v in zip(sites, weights)]
    checks = [[sum(c * y * pow(a, j + t, prime) for a, c, y in zip(sites, dual, row)) % prime
               for j in range(qdim)] for row in extra for t in range(length)]
    qspace = nullspace(checks, qdim, prime)[:width]
    assert len(qspace) == width
    ws = []
    for q in qspace:
        coeffs = [c * sum(qj * pow(a, j, prime) for j, qj in enumerate(q)) % prime
                  for a, c in zip(sites, dual)]
        ws.append([comb(degree, i) * sum(c * pow(a, degree-i, prime)
                                         for c, a in zip(coeffs, sites)) % prime
                   for i in range(degree + 1)])
    reverse_pivots = rref([row[::-1] for row in ws], prime)[1]
    assert len(reverse_pivots) == width
    triangular = width * (width - 1) // 2
    wronskian_degree = sum(degree - i for i in reverse_pivots) - triangular
    ceiling = width * ((d - k if unmasked else degree) - width + 1)
    assert wronskian_degree <= ceiling
    if unmasked:
        assert wronskian_degree == ceiling
    local = (width - errors) * (length - errors)
    assert len(labels) <= ceiling // local
    # Taylor pivot orders give the actual Wronskian order since all degrees are below p.
    total = 0
    for b in range(prime):
        if b == 0:
            jets = ws
        else:
            factors = [[comb(j, i) * pow(b, j-i, prime) % prime for j in range(i, degree+1)]
                       for i in range(degree+1)]
            jets = [[sum(c * f for c, f in zip(row[i:], factors[i])) % prime
                     for i in range(degree + 1)] for row in ws]
        orders = rref(jets, prime)[1]
        actual = sum(orders) - triangular
        if b in labels:
            assert actual >= local, (prime, sites, k, errors, width, b)
        total += actual
    assert total <= wronskian_degree
    return True


def check_domain(prime, sites, counts, broad):
    m = len(sites)
    weights = [1 + (a*a + i + 3) % (prime - 1) for i, a in enumerate(sites)]
    extras = [[(a**3 + 2*i + 1) % prime for i, a in enumerate(sites)],
              [(a*i + 5) % prime for i, a in enumerate(sites)]]
    families = [([1] * m, []), (weights, []), (weights, extras[:1])]
    if broad:
        families.append((weights, extras))
    for k in (range(1, m) if not broad else sorted({1, 2, m//2, m-1})):
        for values, aux in families:
            basis = [[v * pow(a, j, prime) % prime for v, a in zip(values, sites)]
                     for j in range(k)] + aux
            unmasked = all(v == 1 for v in values) and not aux
            for errors in range(min(2 if broad else 1, m-k-1) + 1):
                labels = captured(prime, sites, basis, errors)
                counts[0] += 1
                if not aux:
                    for size in range(k+1, m-errors+1):
                        cap = exact_cap(prime, size, k, unmasked)
                        assert len(labels) <= comb(m, size) * cap // comb(m-errors, size)
                        counts[1] += 1
                # Small fields test all admissible widths. Larger controls use
                # a short and a broad Wronskian to test multiplicity gains.
                widths = range(errors + 1, m-k+1)
                if broad:
                    widths = sorted({errors + 1, (m-k) // (len(aux)+2)})
                for width in widths:
                    if check_wronskian(prime, sites, k, values, aux, errors, width, labels):
                        counts[2] += 1


def main():
    counts = [0, 0, 0]
    for p in (3, 5, 7):
        for m in range(2, (p+1)//2 + 1):
            for sites in combinations(range(p), m):
                check_domain(p, sites, counts, False)
    for p, sites in ((13, (0, 1, 3, 4, 7, 10, 12)),
                     (23, (1, 2, 4, 6, 9, 10, 13, 15, 16, 17, 19, 21)),
                     (41, (0, 1, 4, 7, 11, 13, 15, 18, 19, 23, 27, 30, 37, 39))):
        check_domain(p, sites, counts, True)
    print("membership problems, puncturing bounds, Wronskians checked:", *counts)


if __name__ == "__main__":
    main()
