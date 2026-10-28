#!/usr/bin/env python3
"""Independent re-computation of the order-16 weight-{1,3} spectrum boundary.

Companion to ``probe_order16_weight13_spectrum.py``.  Every step below is written with a
different algorithm from the main probe:

* the 464 signed data are enumerated as ``{-1,0,1}^8`` vectors of Hamming weight 1 or 3
  (instead of support/sign combinations);
* difference norms are Sylvester resultants ``Res(x^8+1, d)`` computed by fraction-free
  elimination on the 15x15 Sylvester matrix (instead of the antipodal-squaring ladder or
  the multiplication-matrix determinant);
* the exceptional prime set is derived from the direct spectrum scan (primes where the
  image cardinality drops below 464), not from factoring norms;
* the MCA bad-scalar sets are computed by brute force over every scalar in ``F_p``
  (instead of the three-point elimination).

All checks are exact integer arithmetic.  Stdlib only; no floats.

Scope.  Same finite-field scope as the main probe: n=16, weights {1,3}, primes
``p = 1 (mod 16)`` up to ``LIMIT``.  No production-regime, maximality, or delta* claim.
"""

from itertools import combinations, product

LIMIT = 20_000
DATA_COUNT = 464
PUBLISHED_NORMS = {
    2, 4, 8, 16, 32, 34, 64, 68, 98, 136, 162, 194, 196, 226, 256, 272, 324, 386, 388,
    392, 452, 482, 512, 514, 544, 578, 674, 706, 772, 776, 784, 802, 866, 898, 904, 964,
    1024, 1028, 1058, 1088, 1154, 1156, 1250, 1282, 1296, 1346, 1348, 1412, 1544, 1552,
    1604, 1666, 1762, 1808, 1858, 1922, 1928, 1954, 2056, 2116, 2306, 2308, 2312, 2372,
    2500, 2564, 2594, 2722, 2818, 2824, 2978, 3076, 3088, 3104, 3136, 3298, 3524, 3592,
    3842, 4096, 4112, 4258, 4352, 4418, 4546, 4624, 4868, 4996, 5378, 5666, 6178, 6562,
    6928, 7108, 8002, 8098, 8194, 9604, 12544, 20736,
}
EXPECTED_COUNTS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272, 353: 272,
    401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368, 673: 416, 769: 416,
    881: 416, 929: 416, 977: 416, 1153: 448, 1217: 448, 1249: 448, 1297: 416,
    1361: 416, 1409: 416, 1489: 416, 1777: 448, 2129: 448, 2273: 448, 2689: 448,
    2833: 448, 3089: 448, 4001: 448, 4049: 448,
}


def signed_data_by_weights():
    data = []
    for vector in product((-1, 0, 1), repeat=8):
        weight = sum(1 for entry in vector if entry)
        if weight in (1, 3):
            data.append(vector)
    return data


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def sylvester_determinant(f, g):
    """Determinant of the Sylvester matrix of f, g (ascending coefficients)."""
    f = trim(f)
    g = trim(g)
    if len(g) == 1 and g[0] == 0:
        return 0
    m = len(f) - 1
    n = len(g) - 1
    size = m + n
    rows = []
    for shift in range(n):
        row = [0] * size
        for i, coefficient in enumerate(f):
            row[i + shift] = coefficient
        rows.append(row)
    for shift in range(m):
        row = [0] * size
        for i, coefficient in enumerate(g):
            row[i + shift] = coefficient
        rows.append(row)
    return bareiss(rows)


def bareiss(matrix):
    size = len(matrix)
    work = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for k in range(size - 1):
        if work[k][k] == 0:
            for r in range(k + 1, size):
                if work[r][k]:
                    work[k], work[r] = work[r], work[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                work[i][j] = (work[i][j] * work[k][k] - work[i][k] * work[k][j]) // previous
        previous = work[k][k]
        for i in range(k + 1, size):
            work[i][k] = 0
    return sign * work[size - 1][size - 1]


def resultant_norm(difference):
    """Res(x^8+1, d) is the norm of d(zeta_16) because x^8+1 is monic."""
    phi = [1, 0, 0, 0, 0, 0, 0, 0, 1]
    return sylvester_determinant(phi, difference)


def primes_one_mod_sixteen(limit):
    def prime(n):
        if n < 2:
            return False
        divisor = 2
        while divisor * divisor <= n:
            if n % divisor == 0:
                return False
            divisor += 1
        return True

    return [p for p in range(17, limit + 1, 16) if prime(p)]


def primitive_root(p):
    factors = set()
    remaining = p - 1
    divisor = 2
    while divisor * divisor <= remaining:
        while remaining % divisor == 0:
            factors.add(divisor)
            remaining //= divisor
        divisor += 1
    if remaining > 1:
        factors.add(remaining)
    for candidate in range(2, p):
        if all(pow(candidate, (p - 1) // q, p) != 1 for q in factors):
            return candidate
    raise AssertionError(f"no primitive root modulo {p}")


def order_sixteen_element(p):
    return pow(primitive_root(p), (p - 1) // 16, p)


def image_size(p, data):
    g = order_sixteen_element(p)
    powers = [pow(g, i, p) for i in range(8)]
    return len({sum(c * powers[i] for i, c in enumerate(vector)) % p for vector in data})


def negative_spectrum(p, data):
    g = order_sixteen_element(p)
    powers = [pow(g, i, p) for i in range(8)]
    values = {sum(c * powers[i] for i, c in enumerate(vector)) % p for vector in data}
    return {(-v) % p for v in values}


def brute_force_bad_scalars(p):
    """Every gamma in F_p is tested; witnesses come from every coordinate pair."""
    g = order_sixteen_element(p)
    domain = [pow(g, k, p) for k in range(16)]
    first_word = [pow(x, 3, p) for x in domain]
    second_word = [pow(x, 2, p) for x in domain]
    lines = []
    for i, j in combinations(range(16), 2):
        slope = (domain[j] - domain[i]) % p
        lines.append((i, j, slope))
    bad = set()
    for gamma in range(p):
        pencil = [(first_word[i] + gamma * second_word[i]) % p for i in range(16)]
        for i, j, spread in lines:
            slope = (pencil[j] - pencil[i]) * pow(spread, -1, p) % p
            intercept = (pencil[i] - slope * domain[i]) % p
            witness = [k for k in range(16)
                       if (intercept + slope * domain[k] - pencil[k]) % p == 0]
            if len(witness) < 3:
                continue
            first_ok = True
            second_ok = True
            slope_f = (first_word[j] - first_word[i]) * pow(spread, -1, p) % p
            icept_f = (first_word[i] - slope_f * domain[i]) % p
            slope_s = (second_word[j] - second_word[i]) * pow(spread, -1, p) % p
            icept_s = (second_word[i] - slope_s * domain[i]) % p
            for k in witness:
                if (icept_f + slope_f * domain[k] - first_word[k]) % p:
                    first_ok = False
                if (icept_s + slope_s * domain[k] - second_word[k]) % p:
                    second_ok = False
                if not first_ok and not second_ok:
                    break
            if not (first_ok and second_ok):
                bad.add(gamma)
                break
    return bad


def main():
    data = signed_data_by_weights()
    assert len(data) == DATA_COUNT, len(data)
    assert all(sum(1 for entry in vector if entry) in (1, 3) for vector in data)

    # Resultant norms over every distinct difference vector (the norm depends only on the
    # difference, so this covers all 107,416 ordered pairs).
    differences = {tuple(a - b for a, b in zip(left, right))
                   for left, right in combinations(data, 2)}
    norms = set()
    for difference in differences:
        assert any(difference)
        norms.add(abs(resultant_norm(list(difference))))
    assert norms == PUBLISHED_NORMS, sorted(norms ^ PUBLISHED_NORMS)

    # Exceptional set from the scan alone.
    primes = primes_one_mod_sixteen(LIMIT)
    counts = {p: image_size(p, data) for p in primes}
    exceptional = {p for p in primes if counts[p] != DATA_COUNT}
    assert exceptional == set(EXPECTED_COUNTS), sorted(exceptional)
    for p in sorted(exceptional):
        assert counts[p] == EXPECTED_COUNTS[p], (p, counts[p])

    # Brute-force census check.
    for p in (17, 97, 113, 1009):
        assert brute_force_bad_scalars(p) == negative_spectrum(p, data), p

    print("order-16 weight-{1,3} spectrum independent cross-check")
    print(f"data (Hamming-weight enumeration): {len(data)}")
    print(f"resultant norms over {len(differences)} distinct differences: "
          f"{len(norms)} distinct values, equal to the published set")
    print(f"scan {len(primes)} primes p = 1 (mod 16) in [17, {LIMIT}]: "
          f"{len(exceptional)} exceptions, counts match the published table")
    print(f"brute-force census at p = 17, 97, 113, 1009: bad set = -spectrum")
    print("PASS: independent implementation reproduces the published integers")


if __name__ == "__main__":
    main()
