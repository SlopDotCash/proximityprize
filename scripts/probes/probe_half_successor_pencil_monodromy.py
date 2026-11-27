#!/usr/bin/env python3
"""Check the group-order and parabolic-index sieves for the two odd split pencils."""

from fractions import Fraction
from math import ceil, comb, isqrt, prod


N = 2**30
D = N // 4 - 1
STAGES = {D, D // 3, D // 5}
PRIMES = (29, 43, 113, 127)
PRODUCTION_FIELDS = (
    365375409332725729550921208179070755120141565953,
    730750818665451459101842416358141509841924915201,
)


def is_prime_power(n):
    """Strip the smallest prime factor, testing whether it is the only one."""
    p = next((i for i in range(2, isqrt(n) + 1) if n % i == 0), n)
    while n % p == 0:
        n //= p
    return n == 1


def gaussian(q, d, k):
    """Number of k-dimensional subspaces of a d-dimensional space over F_q."""
    numerator = prod(q**(d - j) - 1 for j in range(k))
    denominator = prod(q**(j + 1) - 1 for j in range(k))
    return numerator // denominator


def parabolic_indices(q, d):
    """Type, isotropic dimension, and index. Both D+ end vertices are included."""
    for k in range(1, d):
        yield "linear", k, gaussian(q, d, k)
        if 2 * k > d:
            continue
        numerator = prod(q**j - (-1)**j for j in range(d - 2 * k + 1, d + 1))
        denominator = prod(q**(2 * j) - 1 for j in range(1, k + 1))
        yield "unitary", k, numerator // denominator
        r = d // 2
        common = gaussian(q, r, k)
        plus_factors = prod(q**(r - j) + 1 for j in range(k))
        if d % 2:
            yield "odd orthogonal", k, common * plus_factors
        else:
            yield "symplectic", k, common * plus_factors
            split = common * prod(q**(r - j - 1) + 1 for j in range(k))
            yield "orthogonal plus", k, split // 2 if k == r else split
            if k < r:
                yield "orthogonal minus", k, gaussian(q, r - 1, k) * plus_factors


def classical_pairs(degree, primes):
    maximum = degree.bit_length() + 1
    return {
        (q, d) for q in range(2, 114) if is_prime_power(q)
        for d in range(2, maximum + 1) if d <= 6 or q**(d - 2) <= degree
        if all(q % ell == 0 or any(pow(q, i, ell) in (1, ell - 1)
                                    for i in range(1, d + 1)) for ell in primes)
    }


def main():
    for p in PRODUCTION_FIELDS:
        assert (p - 1) % N == 0 and 2 * N * (D + 2) < p
        assert 6**32 < p and 3**32 < p
    for degree, floor in ((D, 44_739_242), (D + 2, 44_739_245)):
        assert (9 * degree - 2 * N + 5) // 6 == floor
        outer = [s for s in range(1, degree // (floor + 1) + 1) if degree % s == 0]
        assert outer == ([1, 3, 5] if degree == D else [1])
        print(f"degree {degree}: subdegree >= {floor}; outer degrees {outer}")
    assert all(m % ell == 0 for m in STAGES for ell in PRIMES)
    pairs = classical_pairs(D, PRIMES)
    assert pairs == ({(2, d) for d in range(14, 30)}
                     | {(4, d) for d in range(7, 16)}
                     | {(16, d) for d in range(7, 9)})
    surviving = set()
    for q, d in sorted(pairs):
        for family, k, index in parabolic_indices(q, d):
            if D % index:
                continue
            assert k == 1 or (family == "linear" and k == d - 1)
            if family == "linear":
                flag_index = gaussian(q, d, 1) * gaussian(q, d - 1, 1)
                assert D % flag_index
            if index in STAGES:
                surviving.add((q, d, family, index))
    assert surviving == {
        (2, 28, "linear", D), (2, 28, "symplectic", D),
        (2, 29, "odd orthogonal", D), (4, 14, "linear", D // 3),
        (4, 14, "symplectic", D // 3), (4, 15, "odd orthogonal", D // 3),
    }
    print(f"{len(pairs)} classical field/dimension pairs; all surviving indices are point actions")
    for item in sorted(surviving):
        print(" ", *item)
    upper = D + 2
    assert upper == 17 * 15_790_321
    assert all(15_790_321 % f for f in range(2, isqrt(15_790_321) + 1))
    high_pairs = classical_pairs(upper, (17, 15_790_321))
    assert high_pairs == ({(2, d) for d in range(28, 31)}
                          | {(4, d) for d in range(14, 17)}
                          | {(16, d) for d in range(7, 10)})
    assert all(upper % index for q, d in high_pairs for _, _, index in parabolic_indices(q, d))
    assert comb(15_790_321, 2) > upper
    print(f"Upper odd degree: all {len(high_pairs)} classical field/dimension pairs eliminated")
    assert comb(127, 6) > D and comb(24_000, 2) > D
    assert not any(comb(a, t) in STAGES for a in range(127, 24_001) for t in range(2, 6))
    assert 2**31 > 2 * D
    print("Each alternating action of an allowed stage degree is natural.")
    for a in (3, 5):
        for b in (3, 5):
            genus = (a - 1) * (b - 1)
            cover_genus = 6 * genus - 3
            bad = 2 * (2 + (2 * a - 2) * (2 * b - 2)) + 1
            upper_height = Fraction(3, 4) * cover_genus * (cover_genus - 1) * (bad - 2)
            lower_height = (a - 2) * (D // a) + (b - 2) * (D // b) - bad
            assert bad <= 133 and upper_height <= 840_627 < 178_956_837 <= lower_height
            c = Fraction(3, 4) * cover_genus * (cover_genus - 1)
            singular = 2 + (2 * a - 2) * (2 * b - 2)
            degree = ceil((lower_height + bad + c + 1) / ((c + 1) * singular + 1))
            assert degree == {(3, 3): 31457, (3, 5): 4959, (5, 5): 761}[tuple(sorted((a, b)))]
    print("Each pair of outer degrees violates the section-height inequality.")


if __name__ == "__main__":
    main()
