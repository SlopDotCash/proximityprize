"""Exact five-core obstruction for the two canonical rate-half fields.

Author: Mikhail Izhutkin (@mashingaan)

The production part checks the algebraic slot census and the two exact prime
fields.  The finite part independently checks every MCA witness on a small
smooth domain by direct Lagrange interpolation.  No floating arithmetic or
third-party package is used.
"""

from math import isqrt


N = 2**30
D = 2**24
K = 2**29
Q = 2**128
P_FIRST = N * (Q + 192) + 1
P_SECOND = N * (2 * Q + 13) + 1
BUDGET_FIRST = N
BUDGET_SECOND = 2 * N


def height(label):
    if label < 31:
        return 5
    if label < 41:
        return (label - 31) // 2
    return 5


def production_slots():
    common = set(range(31))
    groups = [set(range(31 + 2 * j, 33 + 2 * j)) for j in range(5)]
    slots = []
    for j, group in enumerate(groups):
        core = common | group
        assert len(core) == 33
        assert len(core) * D >= K
        for label in range(64):
            if label in core:
                continue
            multiplier = height(label) + j
            assert height(label) != j
            assert 1 <= multiplier <= 9
            slots.append((j, label, multiplier))
    assert len(slots) == 155
    assert len({(label, multiplier) for _, label, multiplier in slots}) == len(slots)
    assert 31 * D + 1 < K
    assert 33 * D + 1 == N - (31 * D - 1)
    assert 4 * 31 * D <= BUDGET_SECOND < 5 * 31 * D
    return slots


def check_production_field(prime, budget):
    slots = production_slots()
    powers = {a: pow(a, N, prime) for a in range(1, 10)}
    assert len(set(powers.values())) == 9
    lower_bound = len(slots) * D
    assert lower_bound > budget
    assert lower_bound * Q > prime
    return {
        "prime": prime,
        "budget": budget,
        "bad_scalar_lower_bound": lower_bound,
        "budget_excess": lower_bound - budget,
        "error_product_excess": lower_bound * Q - prime,
    }


def is_prime(value):
    if value < 2:
        return False
    return all(value % divisor for divisor in range(2, isqrt(value) + 1))


def finite_check():
    n = 128
    d = 2
    k = 64
    prime = next(
        candidate
        for candidate in range(1281, 200000, n)
        if is_prime(candidate)
        and len({pow(a, n, candidate) for a in range(1, 10)}) == 9
    )
    generator = next(
        pow(base, (prime - 1) // n, prime)
        for base in range(2, prime)
        if pow(pow(base, (prime - 1) // n, prime), n // 2, prime) != 1
    )
    points = [pow(generator, i, prime) for i in range(n)]
    roots = [pow(generator, d * label, prime) for label in range(31)]

    def z_at(value):
        result = 1
        for root in roots:
            result = result * (pow(value, d, prime) - root) % prime
        return result

    heights = [height(i % 64) for i in range(n)]
    z_values = [z_at(value) for value in points]
    row_one = [heights[i] * z_values[i] % prime for i in range(n)]
    row_zero = [heights[i] ** 2 * z_values[i] * points[i] % prime for i in range(n)]

    def interpolate(indices, values, point):
        result = 0
        for index in indices:
            numerator = 1
            denominator = 1
            for other in indices:
                if index == other:
                    continue
                numerator = numerator * (point - points[other]) % prime
                denominator = denominator * (points[index] - points[other]) % prime
            result = (result + values[index] * numerator * pow(denominator, -1, prime)) % prime
        return result

    seen = set()
    witnesses = 0
    for j in range(5):
        core = [
            i
            for i in range(n)
            if i % 64 < 31 or i % 64 in (31 + 2 * j, 32 + 2 * j)
        ]
        assert len(core) == 66
        basis = core[:k]
        for i in range(n):
            assert interpolate(basis, row_one, points[i]) == j * z_values[i] % prime
        for i in range(n):
            if i in core:
                continue
            gamma = -(heights[i] + j) * points[i] % prime
            assert len(core) + 1 == 67
            for index in core + [i]:
                left = (j * j * z_values[index] * points[index] + gamma * j * z_values[index]) % prime
                right = (row_zero[index] + gamma * row_one[index]) % prime
                assert left == right
            assert interpolate(basis, row_one, points[i]) != row_one[i]
            assert gamma not in seen
            seen.add(gamma)
            witnesses += 1
    assert witnesses == 310
    return {"prime": prime, "generator": generator, "distinct_scalars": witnesses, "excess_over_2N": witnesses - 2 * n}


if __name__ == "__main__":
    first = check_production_field(P_FIRST, BUDGET_FIRST)
    second = check_production_field(P_SECOND, BUDGET_SECOND)
    finite = finite_check()
    print({"first": first, "second": second, "finite": finite})
