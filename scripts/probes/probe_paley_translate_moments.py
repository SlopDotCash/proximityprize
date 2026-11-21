"""Exact checks of closed-walk pairing and translated Paley block moments."""

from collections import Counter
from itertools import product
from math import prod
from random import Random


def trace_power(matrix, order):
    gram = [[sum(a * b for a, b in zip(u, v)) for v in matrix] for u in matrix]
    power = gram
    for _ in range(1, order):
        cols = list(zip(*gram))
        power = [[sum(a * b for a, b in zip(row, col)) for col in cols] for row in power]
    return sum(row[i] for i, row in enumerate(power))


def check_walks(p, x, y, order):
    character = [0] + [1 if pow(i, (p - 1) // 2, p) == 1 else -1 for i in range(1, p)]
    traces = [0] * p
    square_walks = 0
    walks = 0
    for rows in product(x, repeat=order):
        for cols in product(y, repeat=order):
            labels = [(rows[(i + delta) % order] - cols[i]) % p
                      for i in range(order) for delta in (0, 1)]
            entries = [prod(character[(s + label) % p] for label in labels) for s in range(p)]
            if all(v % 2 == 0 for v in Counter(labels).values()):
                square_walks += 1
            else:
                assert sum(entries) ** 2 <= (2 * order - 1) ** 2 * p
            for s, value in enumerate(entries):
                traces[s] += value
            walks += 1

    n = max(len(x), len(y))
    assert square_walks <= prod(range(1, 2 * order, 2)) * n ** (order + 1)
    for s in range(p):
        matrix = [[character[(a - b + s) % p] for b in y] for a in x]
        assert traces[s] == trace_power(matrix, order)

    # Test the compression to distinct sites with non-unique representations.
    shifts_a = (0, 1)
    shifts_b = (0, 1, 2)
    weights = Counter((a - b) % p for a in shifts_a for b in shifts_b)
    rows = sorted({(a + h) % p for a in x for h in shifts_a})
    cols = sorted({(b + h) % p for b in y for h in shifts_b})
    signed = sum((-1) ** (i + j + j // 3) * character[(a - b) % p]
                 for i, a in enumerate(rows) for j, b in enumerate(cols))
    tu = len(shifts_a) * len(shifts_b)
    # In the proven inequality, the square of the average of ||M_s||^r
    # is bounded by E(T,U) sum_s tr((M_s M_s*)^r) / (tu)^2.
    assert signed ** (2 * order) * tu ** 2 <= (
        (len(rows) * len(cols) * tu) ** order *
        sum(w * w for w in weights.values()) * sum(traces)
    )
    return walks


def main():
    rng = Random(3815)
    walks = cases = 0
    for p in (5, 7, 11, 13, 17):
        for _ in range(6):
            for order in (2, 3):
                x = rng.sample(range(p), rng.randrange(2, 5))
                y = rng.sample(range(p), rng.randrange(2, 5))
                walks += check_walks(p, x, y, order)
                cases += 1
    for ell in (3, 5, 7, 11, 13, 17):
        sites = [2 * ell * j + j * j % ell for j in range(ell)]
        assert len({a - b for a in sites for b in sites if a != b}) == ell * (ell - 1)
        for h in (2, 3, 5):
            domain = [2 * h * d + x for d in sites for x in range(h)]
            assert len(set(domain)) == h * ell
            assert len({a + b for a in domain for b in domain}) == (2*h - 1)*ell*(ell+1)//2
    print(f"{cases} trace comparisons over whole fields, {walks:,} closed walks, 18 Sidon domains")


if __name__ == "__main__":
    main()
