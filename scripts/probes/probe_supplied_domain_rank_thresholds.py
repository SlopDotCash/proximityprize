#!/usr/bin/env python3
"""Compare two support-rank tests with exhaustive decoding on small prime-field RS codes."""

from itertools import combinations, combinations_with_replacement, product
from math import prod


def rank(rows, modulus):
    """Row rank over the prime field, using a normalized row for each pivot."""
    basis = {}
    for original in rows:
        row = [value % modulus for value in original]
        for column in range(len(row)):
            value = row[column]
            if not value:
                continue
            if column not in basis:
                inverse = pow(value, -1, modulus)
                basis[column] = [x * inverse % modulus for x in row]
                break
            row = [(x - value * y) % modulus for x, y in zip(row, basis[column])]
    return len(basis)


def scalar_code(domain, k, q):
    return [
        tuple(sum(a * x**j for j, a in enumerate(coeffs)) % q for x in domain)
        for coeffs in product(range(q), repeat=k)
    ]


def direct_list_sizes(domain, k, m, q):
    scalar = scalar_code(domain, k, q)
    words = [tuple(zip(*rows)) for rows in product(scalar, repeat=m)]
    n = len(domain)
    maxima = [0] * (n + 1)
    for center in product(product(range(q), repeat=m), repeat=n):
        counts = [0] * (n + 1)
        for word in words:
            agreements = sum(x == y for x, y in zip(center, word))
            counts[agreements] += 1
        total = 0
        for t in range(n, -1, -1):
            total += counts[t]
            maxima[t] = max(maxima[t], total)
    return maxima


def distinct_list_count(domain, k, m, q, supports):
    size = len(supports)
    pairs = tuple(combinations(range(size), 2))
    overlap_rows = []
    for a, b in pairs:
        for i in set(supports[a]).intersection(supports[b]):
            row = [0] * (k * size)
            for j in range(k):
                row[k * a + j] = pow(domain[i], j, q)
                row[k * b + j] = -row[k * a + j]
            overlap_rows.append(row)
    total = 0
    for count in range(len(pairs) + 1):
        for edges in combinations(pairs, count):
            rows = list(overlap_rows)
            for a, b in edges:
                for j in range(k):
                    row = [0] * (k * size)
                    row[k * a + j], row[k * b + j] = 1, -1
                    rows.append(row)
            nullity = k * size - rank(rows, q)
            total += (-1) ** count * q ** (m * nullity)
    return total


def list_failure(domain, k, m, q, t, budget):
    supports = tuple(combinations(range(len(domain)), t))
    return any(
        distinct_list_count(domain, k, m, q, pattern) > 0
        for pattern in combinations_with_replacement(supports, budget + 1)
    )


def direct_mca_counts(domain, k, q):
    code = scalar_code(domain, k, q)
    n = len(domain)
    words = list(product(range(q), repeat=n))
    restrictions = {}
    for size in range(n + 1):
        for support in combinations(range(n), size):
            restrictions[support] = {tuple(c[i] for i in support) for c in code}
    maxima = [0] * (n + 1)
    for u, v in product(words, repeat=2):
        counts = [0] * (n + 1)
        for gamma in range(q):
            fold = [(x + gamma * y) % q for x, y in zip(u, v)]
            largest = -1
            for codeword in code:
                agreements = tuple(i for i in range(n) if codeword[i] == fold[i])
                if len(agreements) <= largest:
                    continue
                allowed = restrictions[agreements]
                if any(tuple(w[i] for i in agreements) not in allowed for w in (u, v)):
                    largest = len(agreements)
            for t in range(largest + 1):
                counts[t] += 1
        maxima = [max(a, b) for a, b in zip(maxima, counts)]
    return maxima


def parity_rows(domain, k, q, support):
    """Linear interpolation tests for membership in the restricted RS code."""
    anchors = support[:k]
    rows = []
    for target in support[k:]:
        row = [0] * len(domain)
        row[target] = 1
        for i in anchors:
            other = [domain[j] for j in anchors if i != j]
            numerator = prod(domain[target] - x for x in other)
            denominator = prod(domain[i] - x for x in other)
            row[i] = -numerator * pow(denominator, -1, q) % q
        rows.append(row)
    return rows


def mca_failure(domain, k, q, t, budget):
    # At most k prescribed values always interpolate, so such supports are joint.
    n = len(domain)
    choices = [
        parity_rows(domain, k, q, support)
        for size in range(max(t, k + 1), n + 1)
        for support in combinations(range(n), size)
    ]
    for labels in combinations(range(q), budget + 1):
        for pattern in product(choices, repeat=len(labels)):
            folded = [r + [g * v for v in r] for g, rows in zip(labels, pattern) for r in rows]
            base_rank = rank(folded, q)
            # Once the fold interpolates, both rows interpolate iff the second row does.
            if all(rank(folded + [[0] * n + r for r in rows], q) > base_rank for rows in pattern):
                return True
    return False


def check_equal(actual, expected, case):
    if actual != expected:
        raise AssertionError((case, actual, expected))


def main():
    for q, domain, k, m in [(3, (0, 1, 2), 1, 1), (3, (0, 1, 2), 2, 2),
                            (5, (1, 4, 2), 2, 1)]:
        lists = direct_list_sizes(domain, k, m, q)
        scalars = direct_mca_counts(domain, k, q)
        for t in range(len(domain) + 1):
            for budget in range(4):
                check_equal(list_failure(domain, k, m, q, t, budget), lists[t] > budget,
                            ('list', q, k, m, t, budget))
            for budget in range(q + 1):
                check_equal(mca_failure(domain, k, q, t, budget), scalars[t] > budget,
                            ('MCA', q, k, t, budget))
        print(f'F_{q}, D={domain}, k={k}, width={m}; increasing required agreements')
        print(f'  exhaustive worst list sizes {lists}, worst MCA counts {scalars}; rank tests agree')


if __name__ == '__main__':
    main()
