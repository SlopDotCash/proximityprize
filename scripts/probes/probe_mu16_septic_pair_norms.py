"""Bound all odd prime divisors of the pair-compatibility minors on mu_16."""

from itertools import combinations
from math import prod

from probe_mu32_ratio_norm import PRECISION, chord_intervals
from probe_rate_half_eight_fibers import P as FIRST_PRIME
from probe_second_prime_cyclic_cubics import P as SECOND_PRIME


def check_witnesses(prime):
    base = next(a for a in range(2, 100) if pow(a, (prime - 1) // 2, prime) == prime - 1)
    generator = pow(base, (prime - 1) // 16, prime)
    sites = [pow(generator, i, prime) for i in range(16)]
    assert len(set(sites)) == 16

    def locator(y, roots):
        return prod(y - sites[j] for j in roots) % prime

    def agreement_counts(rows, center):
        return [sum(value == target for value, target in zip(row, center, strict=True))
                for row in rows]

    a, b, c = (0, 1, 8), (2, 9, 10), (3, 5, 7)
    scale = locator(sites[c[0]], a) * pow(locator(sites[c[0]], b), -1, prime) % prime
    available = sorted(set(range(16)) - set(a + b + c))
    common, private = available[:4], available[4:]
    triples = [[0] * 16,
               [locator(y, common + list(a)) for y in sites],
               [scale * locator(y, common + list(b)) % prime for y in sites]]
    center = [0] * 16
    for j in c:
        assert triples[1][j] == triples[2][j]
        center[j] = triples[1][j]
    for i, j in enumerate(private):
        center[j] = triples[i][j]
    assert len(set(map(tuple, triples))) == 3
    assert agreement_counts(triples, center) == [11, 11, 11]

    labels = (0, 1, 3, 7)
    intersections = {(-(i + j)) % 16: k for k, i in enumerate(labels) for j in labels[k+1:]}
    assert len(intersections) == 6
    available = sorted(set(range(16)) - intersections.keys())
    common, private = available[:6], available[6:]
    quartet = [[locator(y, common) * (sites[i] * y + pow(sites[i], -1, prime)) % prime
                for y in sites] for i in labels]
    center = [0] * 16
    for j, k in intersections.items():
        center[j] = quartet[k][j]
    for i, j in enumerate(private):
        center[j] = quartet[i][j]
    assert len(set(map(tuple, quartet))) == 4
    assert agreement_counts(quartet, center) == [10, 10, 10, 10]

    exceptional = range(4)
    row0 = [(-j % prime if j in exceptional else 0) for j in range(16)]
    row1 = [int(j in exceptional) for j in range(16)]
    for gamma in exceptional:
        assert sum((u + gamma * v) % prime == 0 for u, v in zip(row0, row1, strict=True)) == 13
        assert (row0[gamma], row1[gamma]) != (0, 0)
    assert 16 - 4 >= 8 and 16 - 3 - 4 >= 8 and 8 + 6 <= 16 and 8 + 4 <= 16


def main():
    chord = [upper for _, upper in chord_intervals()][::2]
    ceilings = []
    determinant_ceiling = 0
    for degree in range(6):
        maximum = 0
        for roots in combinations(range(16), degree):
            valuation = min(
                sum((i - j) & -(i - j) for j in roots)
                for i in range(16) if i not in roots
            )
            squared_lengths = []
            for t in (1, 3, 5, 7):
                entries = [prod(chord[(t * (i - j)) % 16] for j in roots)
                           for i in range(16)]
                squared_lengths.append(sum(sorted(entries, reverse=True)[:4]))
            bound = prod(squared_lengths)
            shift = 4 * degree * PRECISION + valuation
            exponent = (bound - 1).bit_length() - shift
            fourth_power = (bound**4 - 1).bit_length() - 4 * shift
            determinant_ceiling = max(determinant_ceiling, fourth_power)
            maximum = max(maximum, exponent)
        ceilings.append(maximum)
    assert ceilings == [8, 15, 20, 24, 26, 28], ceilings
    print("Per-column exponents for degrees 0 through 5:", ceilings)
    assert determinant_ceiling == 109
    print("All nonzero pair minors have odd norm at most 2^109.")
    budget_three_prime = (3 * 2**48 + 69) * 2**80 + 1
    assert budget_three_prime // 2**128 == 3
    for p in (budget_three_prime, FIRST_PRIME, SECOND_PRIME):
        check_witnesses(p)
    print("Three field controls: 11 agreements per cubic-locator word, "
          "10 per line-locator word, 13 per bad scalar in the four-spike pair.")


if __name__ == "__main__":
    main()
