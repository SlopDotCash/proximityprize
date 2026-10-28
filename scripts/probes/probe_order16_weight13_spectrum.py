#!/usr/bin/env python3
"""Order-16 signed weight-{1,3} spectrum: exact collision set and n=16 ceiling counts.

Extends the order-eight (h=4) boundary of ``g330_spectrum_exact_boundary.py`` /
``Frontier/_G330SpectrumExactBoundary.lean`` one rung up, to h=8 (n=16), and ties the
spectrum count to the dimension-two MCA census of the KKH26 ceiling stack.

Object.  For a prime field ``F_p`` containing an order-16 element ``g``, let ``D`` be the
464 signed data of support size 1 or 3 over the half-window ``{g^0, ..., g^7}`` (16 data of
weight 1, 448 of weight 3).  The signed-sum value of a datum is
``sum_{i in T} g^i - sum_{i in U\\T} g^i``.  The KKH26 counting core consumes injectivity of
this map (``subsetSumSpectrum_card`` with valid weights ``{1,3}``), which yields the exact
spectrum size ``2 * C(8,1) + 2^3 * C(8,3) = 16 + 448 = 464``.

What this probe certifies, by exact integer arithmetic only:

1. Reproduction at h=4: the 40 signed data, their 780 pairwise difference norms, the
   published norm set, and the scan ``p = 1 (mod 8), p <= 20000`` with ``p=17 -> 16`` values
   and every other prime ``-> 40`` (the G330 integers).
2. At h=8 the 107,416 pairwise difference norms take exactly 100 distinct values; two
   independent norm algorithms (the antipodal-squaring ladder and an 8x8 multiplication-
   matrix determinant) agree on every pair.
3. The primes ``= 1 (mod 16)`` dividing those norms are exactly the 34-element set ``E16``
   (largest 4049), and every member is prime.
4. Scan: for every prime ``p = 1 (mod 16)`` in ``[17, 20000]`` the spectrum has exactly 464
   values iff ``p`` is not in ``E16``; at each exceptional prime the count is the tabulated
   value (17 to 448).  So the h=8 collision boundary is the 34-prime set ``E16``, not a
   single prime as at h=4.
5. Census: for the KKH26 ceiling stack ``(x^3, x^2)`` at agreement threshold 3 on ``mu_16``,
   the MCA bad-scalar set equals the negated spectrum set exactly at every checked prime
   (all 34 exceptional primes, the ordinary primes 1009 and 1201, and the six smallest primes
   ``= 1 (mod 16)`` above 4049).  Hence that stack's bad-scalar count is the spectrum
   cardinality at those primes.

Scope.  Finite fields only, ``n = 16``, weights ``{1,3}``.  The probe does not prove a
field-uniform census theorem: the exclusion direction away from ``E16`` is the in-tree
divisibility route (``not_isRoot_of_not_dvd_resultant``, the engine behind
``sVal_injOn_of_not_dvd``) instantiated at ``m = 4`` with the computed norms, and the
inclusion direction is exhibited per exceptional prime.  Nothing here is a statement about
the production regime (``n = 2^30``), about maximality of the count over all stacks, about
weights other than ``{1,3}``, or about ``delta*``.  Stdlib only; no floats.
"""

from itertools import combinations

LIMIT = 20_000

# Published h=4 integers (G330).
G330_DATA_COUNT = 40
G330_PAIR_COUNT = 780
G330_NORMS = {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 144}
G330_EXCEPTION = {17: 16}
G330_STABLE = 40

# h=8 integers computed by this probe.
H8_DATA_COUNT = 464
H8_PAIR_COUNT = 107_416
H8_NORMS = {
    2, 4, 8, 16, 32, 34, 64, 68, 98, 136, 162, 194, 196, 226, 256, 272, 324, 386, 388,
    392, 452, 482, 512, 514, 544, 578, 674, 706, 772, 776, 784, 802, 866, 898, 904, 964,
    1024, 1028, 1058, 1088, 1154, 1156, 1250, 1282, 1296, 1346, 1348, 1412, 1544, 1552,
    1604, 1666, 1762, 1808, 1858, 1922, 1928, 1954, 2056, 2116, 2306, 2308, 2312, 2372,
    2500, 2564, 2594, 2722, 2818, 2824, 2978, 3076, 3088, 3104, 3136, 3298, 3524, 3592,
    3842, 4096, 4112, 4258, 4352, 4418, 4546, 4624, 4868, 4996, 5378, 5666, 6178, 6562,
    6928, 7108, 8002, 8098, 8194, 9604, 12544, 20736,
}
H8_PRIME_DIVISORS = {
    2, 3, 5, 7, 17, 23, 31, 47, 97, 113, 193, 241, 257, 337, 353, 401, 433, 449, 577,
    593, 641, 673, 769, 881, 929, 977, 1153, 1217, 1249, 1297, 1361, 1409, 1489, 1777,
    2129, 2273, 2689, 2833, 3089, 4001, 4049,
}
H8_EXCEPTIONS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272, 353: 272,
    401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368, 673: 416, 769: 416,
    881: 416, 929: 416, 977: 416, 1153: 448, 1217: 448, 1249: 448, 1297: 416,
    1361: 416, 1409: 416, 1489: 416, 1777: 448, 2129: 448, 2273: 448, 2689: 448,
    2833: 448, 3089: 448, 4001: 448, 4049: 448,
}


def signed_data(h, weights):
    data = []
    for a in weights:
        for support in combinations(range(h), a):
            for size in range(a + 1):
                for negatives in combinations(support, size):
                    coefficients = [0] * h
                    for i in support:
                        coefficients[i] = -1 if i in negatives else 1
                    data.append(tuple(coefficients))
    return data


def ring_mul(left, right):
    h = len(left)
    out = [0] * h
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                k = i + j
                if k >= h:
                    out[k - h] -= a * b
                else:
                    out[k] += a * b
    return out


def cyclotomic_norm(coeffs):
    """Norm over Q(zeta_{2h}) by repeated antipodal squaring (h a power of two)."""
    current = list(coeffs)
    conjugation = [c if i % 2 == 0 else -c for i, c in enumerate(current)]
    while len(current) > 2:
        product = ring_mul(current, conjugation)
        assert all(product[i] == 0 for i in range(1, len(product), 2))
        current = [product[2 * j] for j in range(len(current) // 2)]
        conjugation = [c if i % 2 == 0 else -c for i, c in enumerate(current)]
    return current[0] * current[0] + current[1] * current[1]


def det_bareiss(matrix):
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


def determinant_norm(coeffs):
    """Norm over Q(zeta_{2h}) as the determinant of multiplication by ``coeffs``."""
    h = len(coeffs)
    basis = [[1 if i == j else 0 for i in range(h)] for j in range(h)]
    columns = [ring_mul(coeffs, e) for e in basis]
    matrix = [[columns[c][r] for c in range(h)] for r in range(h)]
    return det_bareiss(matrix)


def primes_congruent_to(limit, residue, modulus):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    divisor = 2
    while divisor * divisor <= limit:
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start::divisor] = b"\x00" * (((limit - start) // divisor) + 1)
        divisor += 1
    return [p for p in range(2, limit + 1) if sieve[p] and p % modulus == residue]


def element_of_exact_order(p, order):
    for candidate in range(2, p):
        g = pow(candidate, (p - 1) // order, p)
        if pow(g, order // 2, p) == p - 1:
            return g
    raise AssertionError(f"no element of order {order} modulo {p}")


def spectrum_image(g, p, data):
    return {sum(c * pow(g, i, p) for i, c in enumerate(datum)) % p for datum in data}


def is_affine_on(values, indices, domain, p):
    first, second = indices[0], indices[1]
    slope = (values[second] - values[first]) * pow(domain[second] - domain[first], -1, p) % p
    intercept = (values[first] - slope * domain[first]) % p
    return all((intercept + slope * domain[i] - values[i]) % p == 0 for i in indices)


def bad_scalars(p, g, threshold=3, first_exp=3, second_exp=2):
    """Bad scalars of the monomial-pencil stack (x^first_exp, x^second_exp) on <g>."""
    n = 16
    domain = [pow(g, k, p) for k in range(n)]
    first_word = [pow(x, first_exp, p) for x in domain]
    second_word = [pow(x, second_exp, p) for x in domain]

    candidates = set()
    for i, j, k in combinations(range(n), 3):
        a11 = (domain[j] - domain[i]) % p
        a12 = (-(second_word[j] - second_word[i])) % p
        a21 = (domain[k] - domain[i]) % p
        a22 = (-(second_word[k] - second_word[i])) % p
        b1 = (first_word[j] - first_word[i]) % p
        b2 = (first_word[k] - first_word[i]) % p
        determinant = (a11 * a22 - a12 * a21) % p
        if determinant:
            candidates.add((a11 * b2 - b1 * a21) * pow(determinant, -1, p) % p)

    bad = set()
    for gamma in candidates:
        pencil = [(first_word[i] + gamma * second_word[i]) % p for i in range(n)]
        witnesses = set()
        for i, j in combinations(range(n), 2):
            slope = (pencil[j] - pencil[i]) * pow(domain[j] - domain[i], -1, p) % p
            intercept = (pencil[i] - slope * domain[i]) % p
            witnesses.add(tuple(k for k in range(n)
                                if (intercept + slope * domain[k] - pencil[k]) % p == 0))
        if any(len(w) >= threshold
               and not (is_affine_on(first_word, list(w), domain, p)
                        and is_affine_on(second_word, list(w), domain, p))
               for w in witnesses):
            bad.add(gamma)
    return bad


def factor(n):
    n = abs(n)
    factors = set()
    divisor = 2
    while divisor * divisor <= n:
        while n % divisor == 0:
            factors.add(divisor)
            n //= divisor
        divisor += 1 if divisor == 2 else 2
    if n > 1:
        factors.add(n)
    return factors


def is_prime(n):
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 1
    return True


def norm_set(data):
    norms = set()
    for left, right in combinations(data, 2):
        difference = tuple(x - y for x, y in zip(left, right))
        assert any(difference)
        ladder = cyclotomic_norm(difference)
        assert abs(ladder) == abs(determinant_norm(difference)), (difference, ladder)
        norms.add(abs(ladder))
    return norms


def reproduce_h4():
    data = signed_data(4, (1, 3))
    assert len(data) == len(set(data)) == G330_DATA_COUNT
    assert len(list(combinations(data, 2))) == G330_PAIR_COUNT
    assert norm_set(data) == G330_NORMS
    for p in primes_congruent_to(LIMIT, 1, 8):
        g = element_of_exact_order(p, 8)
        count = len(spectrum_image(g, p, data))
        if p in G330_EXCEPTION:
            assert count == G330_EXCEPTION[p], (p, count)
        else:
            assert count == G330_STABLE, (p, count)


def main():
    # 1. Reproduce the published h=4 integers exactly.
    reproduce_h4()

    # 2. h=8 norms, two algorithms on every pair.
    data = signed_data(8, (1, 3))
    assert len(data) == len(set(data)) == H8_DATA_COUNT
    assert len(list(combinations(data, 2))) == H8_PAIR_COUNT
    norms = norm_set(data)
    assert norms == H8_NORMS, sorted(norms - H8_NORMS) or sorted(H8_NORMS - norms)

    # 3. Exact prime divisors and the exceptional set.
    divisors = set()
    for value in norms:
        divisors |= factor(value)
    assert divisors == H8_PRIME_DIVISORS, sorted(divisors)
    exceptions = {q for q in divisors if q % 16 == 1}
    assert exceptions == set(H8_EXCEPTIONS), sorted(exceptions)
    assert all(is_prime(q) for q in exceptions)
    assert max(exceptions) == 4049

    # 4. Collision scan over every prime p = 1 (mod 16) up to LIMIT.
    primes = primes_congruent_to(LIMIT, 1, 16)
    assert primes[0] == 17
    counts = {}
    for p in primes:
        g = element_of_exact_order(p, 16)
        counts[p] = len(spectrum_image(g, p, data))
    assert {p for p in primes if counts[p] != H8_DATA_COUNT} == exceptions
    for p in sorted(exceptions):
        assert counts[p] == H8_EXCEPTIONS[p], (p, counts[p])

    # 5. MCA census of the KKH26 ceiling stack (x^3, x^2) at threshold 3.
    checked = sorted(exceptions)
    checked += [p for p in primes if 17 <= p <= 1201 and p not in exceptions]
    checked += [p for p in primes if p > 4049][:6]
    for p in checked:
        g = element_of_exact_order(p, 16)
        image = spectrum_image(g, p, data)
        negated = {(-v) % p for v in image}
        assert bad_scalars(p, g) == negated, p

    print("order-16 signed weight-{1,3} spectrum certificate")
    print(f"h=4 reproduction: {G330_DATA_COUNT} data, {G330_PAIR_COUNT} pairs, "
          f"norms {sorted(G330_NORMS)}; scan -> 40 except p=17 -> 16")
    print(f"h=8: {H8_DATA_COUNT} data, {H8_PAIR_COUNT} pairs, "
          f"{len(norms)} distinct norms (two norm algorithms agree on all pairs)")
    print(f"primes = 1 (mod 16) dividing a norm: {len(exceptions)} "
          f"(max {max(exceptions)}); spectrum is 464 elsewhere")
    print(f"scan: {len(primes)} primes p = 1 (mod 16) in [17, {LIMIT}]; "
          f"exceptions {sorted(exceptions)}")
    print("exception counts: "
          + ", ".join(f"{p}:{H8_EXCEPTIONS[p]}" for p in sorted(exceptions)))
    print(f"MCA ceiling (x^3, x^2), threshold 3: bad set = -spectrum at "
          f"{len(checked)} primes (34 exceptional + sample)")
    print("PASS: the order-16 weight-{1,3} collision boundary is the 34-prime set above")


if __name__ == "__main__":
    main()
