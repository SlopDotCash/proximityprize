#!/usr/bin/env python3
"""Compute full 2-primary Smith factors from compressed subgroup products."""

from itertools import combinations
from math import comb, gcd
from random import Random

FIELDS = (
    (365375409332725729550921208179070755120141565953,
     303645430271030343624574566109998498685964493478, 3,
     [400, 176, 452, 440, 54, 290], [28, 28, 30, 30, 32, 35]),
    (730750818665451459101842416358141509841924915201,
     192152681249815148642741928588691886362054863855, 29,
     [0, 0, 6, 4, 6, 0], [29, 29, 30, 30, 30, 30]),
)


def multiply(left, right, relation, modulus):
    """Multiply in the power basis modulo a monic sextic with given tail."""
    product = [0] * 11
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product[i + j] += a * b
    for degree in range(10, 5, -1):
        for i, coefficient in enumerate(relation):
            product[degree - 6 + i] -= product[degree] * coefficient
    return [a % modulus for a in product[:6]]


def remainder(coefficients, relation, modulus):
    """Reduce a polynomial in X = 1 + T against the sextic in T by Horner."""
    tail = [0] * 6
    for coefficient in reversed(coefficients):
        high = tail[-1]
        shifted = [coefficient + tail[0]]
        shifted.extend(tail[i] + tail[i - 1] for i in range(1, 6))
        tail = [(x - high * y) % modulus for x, y in zip(shifted, relation)]
    return tail


def prepare(coefficients, bits):
    """Lift the monic factor reducing to T^6 by its polynomial remainders."""
    hasse = [sum(x for j, x in enumerate(coefficients) if j & i == i) % 2
             for i in range(12)]
    assert hasse[:7] == [0] * 6 + [1]
    corrections = {}
    for mask in range(64):
        delta = [(mask >> i) & 1 for i in range(6)]
        image = multiply(delta, hasse[6:], [0] * 6, 2)
        corrections[tuple(image)] = delta
    assert len(corrections) == 64
    relation = [0] * 6
    for k in range(1, bits):
        current = remainder(coefficients, relation, 2**(k + 1))
        assert all(x % 2**k == 0 for x in current)
        delta = corrections[tuple(x // 2**k for x in current)]
        relation = [x + 2**k * y for x, y in zip(relation, delta)]
    assert not any(remainder(coefficients, relation, 2**bits))
    return relation


def smith_valuations(matrix, bits):
    """Smith exponents over Z/2^bits, with exponent bits denoting zero."""
    size = len(matrix)
    modulus = 2**bits
    valuations = []
    for k in range(size):
        entries = ((matrix[i][j], i, j) for i in range(k, size) for j in range(k, size))
        order, i, j = min(((x & -x).bit_length() - 1 if x else bits, i, j)
                          for x, i, j in entries)
        if order == bits:
            return valuations + [bits] * (size - k)
        valuations.append(order)
        matrix[k], matrix[i] = matrix[i], matrix[k]
        for row in matrix:
            row[k], row[j] = row[j], row[k]
        inverse = pow(matrix[k][k] >> order, -1, modulus)
        for row in matrix[k + 1:]:
            scale = (row[k] >> order) * inverse % modulus
            for j in range(k, size):
                row[j] = (row[j] - scale * matrix[k][j]) % modulus
        # Clearing the pivot row by column operations leaves the remaining block intact.
    return valuations


def determinant(rows):
    """Compute the exact integer determinant by expansion in the first row."""
    if not rows:
        return 1
    return sum((-1)**j * value * determinant([row[:j] + row[j+1:] for row in rows[1:]])
               for j, value in enumerate(rows[0]) if value)


def smith_by_minors(matrix, bits):
    """Compute capped Smith exponents independently via integer determinantal divisors."""
    size = len(matrix)
    exponents = []
    previous = 0
    for width in range(1, size + 1):
        divisor = 0
        sets = list(combinations(range(size), width))
        for rows in sets:
            for columns in sets:
                minor = [[matrix[i][j] for j in columns] for i in rows]
                divisor = gcd(divisor, determinant(minor))
        if not divisor:
            return exponents + [bits] * (size - len(exponents))
        valuation = (divisor & -divisor).bit_length() - 1
        exponents.append(min(bits, valuation - previous))
        previous = valuation
    return exponents


def compressed_smith(blocks, exponent, precision, verify_minors=False):
    """Compute the six nonunit exponents at length 2^exponent."""
    rest = precision - exponent + 2
    assert rest >= 1 and exponent >= 3
    relation = prepare(blocks, rest + 1)
    modulus = 2**rest
    initial = remainder([-1] + [0] * 7 + [1], relation, 2 * modulus)
    assert all(x % 2 == 0 for x in initial)
    normalized = [x // 2 for x in initial]
    for k in range(3, exponent):
        square = multiply(normalized, normalized, relation, modulus)
        normalized = [(x + 2**(k - 3) * y) % modulus for x, y in zip(normalized, square)]
    basis = [[int(i == j) for j in range(6)] for i in range(6)]
    matrix = [multiply(normalized, row, relation, modulus) for row in basis]
    orders = smith_valuations([row[:] for row in matrix], rest)
    if verify_minors:
        assert orders == smith_by_minors(matrix, rest)
    return relation, [exponent - 2 + k for k in orders]


def named_fields():
    n = 2**30
    for p, g, nonresidue, expected_relation, expected_orders in FIELDS:
        precision = ((p - 1) & (1 - p)).bit_length() - 1
        bits = precision - 27
        count = 2**(bits + 2)
        assert pow(g, n // 2, p) == p - 1
        char_exp = (p - 1) // 2**bits
        generator = pow(nonresidue, char_exp, p)
        logs = {pow(generator, j, p): j for j in range(2**bits)}
        assert len(logs) == 2**bits
        root = pow(g, n // count, p)
        factors = [n // count] + [1 - pow(root, j, p) for j in range(1, count)]
        blocks = [logs[pow(factor % p, char_exp, p)] for factor in factors]
        relation, orders = compressed_smith(blocks, 30, precision, verify_minors=True)
        assert relation == expected_relation and orders == expected_orders
        print(f"p={p} blocks={count} mod 2^{precision}: sextic={relation}, orders={orders}")


def compare_dense():
    random = Random(311)
    comparisons = 0
    base = [comb(6, i) * (-1)**(6 - i) for i in range(7)]
    for exponent in (4, 5, 6, 7):
        n = 2**exponent
        for rest in (1, 2, 3):
            precision = exponent - 2 + rest
            modulus = 2**precision
            count = min(n, 2**(rest + 3))
            for _ in range(3):
                unit = [random.randrange(2) for _ in range(n)]
                unit[0] = (1 - sum(unit[1:])) % 2
                kernel = [sum(x * unit[(j-i) % n] for i, x in enumerate(base))
                          + 2 * random.randrange(modulus) for j in range(n)]
                blocks = [sum(kernel[j::count]) % 2**(rest + 1) for j in range(count)]
                _, predicted = compressed_smith(blocks, exponent, precision)
                matrix = [[kernel[(i-j) % n] % modulus for j in range(n)] for i in range(n)]
                assert smith_valuations(matrix, precision) == [0] * (n - 6) + predicted
                comparisons += 1
    print(f"{comparisons} dense Smith comparisons passed")


if __name__ == "__main__":
    named_fields()
    compare_dense()
