"""Check the rank and degree obstructions for permuted binary hyperplane masks."""
from itertools import combinations, product
from random import Random


def echelon(rows, columns, prime):
    """Return row echelon form with pivot columns over the given prime field."""
    basis = {}
    for row in rows:
        row = [v % prime for v in row]
        for col in range(columns):
            if not row[col]:
                continue
            if col not in basis:
                inverse = pow(row[col], -1, prime)
                basis[col] = [v * inverse % prime for v in row]
                break
            factor = row[col]
            row = [(v - factor * w) % prime for v, w in zip(row, basis[col], strict=True)]
    return basis


def line_relation_control():
    # Normalise each first entry to 1. All three entries must be nonzero,
    # and the row must kill the constant vector.
    lines = [tuple(a-1 for a in range(1, 8) if (a & x).bit_count() % 2 == 0)
             for x in range(1, 8)]
    for prime in (3, 5):
        counts = {}
        for values in product(range(1, prime - 1), repeat=7):
            rows = []
            for (i, j, k), alpha in zip(lines, values, strict=True):
                row = [0] * 7
                row[i], row[j], row[k] = 1, alpha, -1-alpha
                rows.append(row)
            basis = echelon(rows, 7, prime)
            rank = len(basis)
            counts[rank] = counts.get(rank, 0) + 1
            if rank < 5:
                # The rank lemma uses pairwise distinct columns in the
                # kernel representation; rank-deficient controls must violate it.
                column_equal = False
                for i, j in combinations(range(7), 2):
                    difference = [0] * 7
                    difference[i], difference[j] = 1, -1
                    if len(echelon([*basis.values(), difference], 7, prime)) == rank:
                        column_equal = True
                        break
                assert column_equal
        print(f'F_{prime} line matrices by rank: {counts}')


def mask_control(prime, b, seed):
    """Test actual polynomial compatibility by eliminating the received symbols."""
    rng = Random(seed)
    points = rng.sample(range(prime), 8*b)
    classes = [points[i:i+b] for i in range(0, 8*b, b)]
    covers = []
    for a in range(1, 8):
        support = {x for i, block in enumerate(classes) if (i & a).bit_count() % 2 == 0
                   for x in block}
        support.difference_update(rng.sample(sorted(support), 2))
        covers.append(support)

    # Quotient out the common polynomial by fixing the first word to zero.
    degree_bound = 2 * b
    columns = 6 * degree_bound
    rows = []
    for x in points:
        matched = [i for i in range(7) if x in covers[i]]
        if len(matched) < 2:
            continue
        powers = [pow(x, k, prime) for k in range(degree_bound)]
        for other in matched[1:]:
            row = [0] * columns
            for idx, sign in ((matched[0], -1), (other, 1)):
                if idx:
                    start = (idx - 1) * degree_bound
                    row[start:start+degree_bound] = [sign * v for v in powers]
            rows.append(row)
    rank = len(echelon(rows, columns, prime))
    assert rank == columns
    print(f'F_{prime}, {8*b} reindexed sites, seed {seed}: '
          f'all {columns} relative coefficients forced to zero')


def trace_control():
    # Polynomial basis for F_16 modulo X^4 + X + 1.
    def multiply(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & 16:
                a ^= 19
        return result

    def power(a, exponent):
        result = 1
        for _ in range(exponent):
            result = multiply(result, a)
        return result

    leading = set()
    for alpha in range(1, 16):
        scale = power(power(alpha, 8), 14)
        coefficients = {j-1: multiply(scale, power(alpha, j)) for j in (1, 2, 4)}
        leading.add(coefficients[3])
        mask = []
        for x in range(16):
            ax = multiply(alpha, x)
            trace = ax ^ power(ax, 2) ^ power(ax, 4) ^ power(ax, 8)
            assert trace in (0, 1)
            if trace == 0 and x:
                value = 0
                for j, coefficient in coefficients.items():
                    value ^= multiply(coefficient, power(x, j))
                assert value == power(x, 7)
                mask.append(x)
        assert len(mask) == 7
    assert len(leading) == 15
    print('F_16 trace center: all 15 distinct cubic words realize the homogeneous masks.')


def main():
    trace_control()
    line_relation_control()
    for seed in (17, 29, 311):
        mask_control(257, 8, seed)
    b = 2**27
    max_deletions = (b + 5) // 63
    assert max_deletions == 2_130_440
    for h in (2, max_deletions):
        c = 10*h - 1
        assert 7*(b - 3*h - 5*c) > b + 7*h - 1
    assert 63 * (max_deletions + 1) >= b + 6
    print(f'Production inequality checked through {max_deletions:,} deletions per mask.')


if __name__ == '__main__':
    main()
