"""Certify the order-16 pair ranks and independently check every reported maximizer."""
from functools import cache
from itertools import combinations, permutations
from math import comb, gcd
from pathlib import Path
import subprocess
import tempfile


MAXIMA = {
    (2, 3, 3): 32983201, (2, 3, 4): 328634577, (2, 4, 4): 2549502401,
    (2, 4, 5): 13195144609, (2, 5, 5): 36740277089,
    (3, 3, 4): 15527402881, (3, 4, 4): 212569315681,
    (3, 4, 5): 1312108393729, (3, 5, 5): 3060803059969,
    (4, 4, 4): 30728141630209, (4, 5, 5): 33844696351656961,
    (5, 4, 4): 13786369, (5, 5, 5): 43046721,
}
ONE = (1, 0, 0, 0, 0, 0, 0, 0)
ZERO = (0,) * 8


def require(condition, message):
    if not condition:
        raise ValueError(message)


def power(e):
    return tuple(((-1) ** ((e % 16) // 8)) * int(i == e % 8) for i in range(8))


def multiply(a, b):
    c = [0] * 8
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[(i + j) % 8] += (1 if i + j < 8 else -1) * x * y
    return tuple(c)


def locator(site, mask):
    v = ONE
    for j in range(16):
        if (mask >> j) & 1:
            v = multiply(v, tuple(a - b for a, b in zip(power(site), power(j), strict=True)))
    return v


def odd_norm(rows):
    # Leibniz determinant, followed by the determinant of multiplication on Z[z].
    n = len(rows)
    value = [0] * 8
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i, j in combinations(range(n), 2))
        term = ONE
        for i, j in enumerate(perm):
            term = multiply(term, rows[i][j])
        for k, x in enumerate(term):
            value[k] += (-1) ** inversions * x
    mat = [list(multiply(value, power(j))) for j in range(8)]
    denominator = 1
    for i in range(7):
        pivot = next((j for j in range(i, 8) if mat[j][i]), None)
        if pivot is None:
            return 0
        mat[i], mat[pivot] = mat[pivot], mat[i]
        for j in range(i + 1, 8):
            for k in range(i + 1, 8):
                numerator = mat[j][k] * mat[i][i] - mat[j][i] * mat[i][k]
                require(numerator % denominator == 0, "inexact Bareiss division")
                mat[j][k] = numerator // denominator
        denominator = mat[i][i]
    norm = abs(mat[-1][-1])
    return norm // (norm & -norm) if norm else 0


def check_witness(n, row_mask, a, b, single_power, omitted):
    sites = [i for i in range(16) if (row_mask >> i) & 1]
    require(len(sites) == n and not (row_mask & (a | b) or a & b), "overlapping support")
    matrix = []
    for i, site in enumerate(sites):
        left, right = locator(site, a), locator(site, b)
        singleton = ZERO if i == omitted else multiply(power(single_power * site), right)
        if n == 2:
            row = [left, singleton]
        elif n == 3:
            row = [left, multiply(power(site), left), singleton]
        else:
            row = [left, multiply(power(site), left), right, multiply(power(site), right)]
        matrix.append(row)
    if n == 5:
        return gcd(*(odd_norm(rows) for rows in combinations(matrix, 4)))
    return odd_norm(matrix)


@cache
def orbit_count(n):
    unseen = set(combinations(range(16), n))
    count = 0
    while unseen:
        y = unseen.pop()
        unseen.difference_update(tuple(sorted((u * i + v) % 16 for i in y))
                                 for u in range(1, 16, 2) for v in range(16))
        count += 1
    return count


def main():
    source = Path(__file__).with_suffix(".cpp")
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp) / "census"
        subprocess.run(["c++", "-std=c++17", "-O3", "-Wall", "-Wextra", "-Werror",
                        str(source), "-o", str(binary)], check=True)
        output = subprocess.check_output([str(binary)], text=True)
    seen = set()
    for line in output.splitlines():
        n, a, b, count, maximum, mask, first, second, exponent, omitted = map(int, line.split())
        key = n, a, b
        require(key not in seen and maximum == MAXIMA[key], "census maximum")
        seen.add(key)
        pairs = orbit_count(n) * comb(16 - n, a) * comb(16 - n - a, b)
        variants = 3 if n == 2 else (2 if a == b else 4)
        expected = pairs * variants if n < 4 else pairs // 2
        require(count == expected, "incomplete orbit census")
        require(first.bit_count() == a and second.bit_count() == b, "witness degrees")
        require(check_witness(n, mask, first, second, exponent, omitted) == maximum,
                "independent determinant or norm disagrees")
        print(f"rows={n} degrees={a},{b} cases={count} max={maximum}")
    require(seen == set(MAXIMA), "missing cases")
    bound = max(v for (n, _, _), v in MAXIMA.items() if n != 4)
    require(bound**3 < 3 * 2**128, "cubic-index coverage")
    for k, t, index in [(31, 60, 2), (305, 35, 3)]:
        p = k * 2**t + 1
        require(k < 2**t and k % 2 and pow(3, (p - 1) // 2, p) == p - 1,
                "Proth certificate")
        require(p % 16 == 1 and p**index // 2**128 == 3 and bound < p < 2**109,
                "example outside previous characteristic range")
    print(f"All required pair ranks transfer for residue-field size greater than {bound}.")


if __name__ == "__main__":
    main()
