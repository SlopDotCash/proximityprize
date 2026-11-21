#!/usr/bin/env python3
"""Certify a dyadic, field-generating obstruction to the workbench Shaw bound.

Let n = 2m be a power of two and p > n a prime with v_2(p-1) = log_2 m.
Take a nonsquare a of order m in F_p and u² = a in F_{p²}. The powers of
u form H of order n, and u generates the quadratic field. The functional
L(c+du) = d induces a nontrivial additive character. At the nonzero scalar
frequencies t in F_p, the period is m + sum_{z in <a>} exp(2 pi i t z/p).
As t varies, each nonzero residue occurs m times in the latter sum. Its
mean is -m/(p-1). Hence some period has modulus at least m-m/(p-1).

The small anchor enumerates the field and exponent histogram. The large
anchor certifies the prime, a, field-size bracket, and a strict lower bound
on the Shaw constant by integer arithmetic. It uses the mean argument
above instead of enumerating the large field.
"""

from collections import Counter
from fractions import Fraction
from itertools import product

from verify_g139_n2e30_arithmetic_contract import is_prime_u64, verify_pocklington_prime


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify_generator(p, n, base):
    m = n // 2
    require(n >= 4 and n & (n - 1) == 0, "expected a dyadic order")
    require(p > n and p % n == m + 1, "incorrect quadratic order parameters")
    a = pow(base, (p - 1) // m, p)
    require(pow(a, m, p) == 1 and pow(a, m // 2, p) == p - 1, "wrong base-field order")
    require(pow(a, (p - 1) // 2, p) == p - 1, "quadratic polynomial is reducible")
    return a


def verify_small_field():
    p, n = 13, 8
    m = n // 2
    require(is_prime_u64(p), "small characteristic is composite")
    a = verify_generator(p, n, 2)

    def multiply(x, y):
        c, d = x
        e, f = y
        return ((c * e + a * d * f) % p, (c * f + d * e) % p)

    def power(x, k):
        result = (1, 0)
        for _ in range(k):
            result = multiply(result, x)
        return result

    coordinates = range(p)
    roots = {x for x in product(coordinates, repeat=2) if power(x, n) == (1, 0)}
    require(len(roots) == n, "incorrect root count")
    require(roots == {power((0, 1), j) for j in range(n)}, "missing powers of u")
    histogram = Counter(t * d % p for t in range(1, p) for _, d in roots)
    require(histogram[0] == (p - 1) * m, "wrong multiplicity at zero")
    require(all(histogram[t] == m for t in range(1, p)), "wrong nonzero multiplicity")
    print(f"F_{p}², |H|={n}, exponent multiplicities 0:{histogram[0]}, nonzero:{m}")


def verify_large_anchor():
    n = 1 << 30
    m = n // 2
    p = 1 + m * ((1 << 50) + 7)
    factors = (2,) * 29 + (37, 30429727211963)
    require(all(is_prime_u64(t) for t in set(factors)), "nonprime certificate factor")
    verify_pocklington_prime(p, factors, {2: 3, 37: 2, 30429727211963: 2})
    a = verify_generator(p, n, 3)
    q = p * p
    require(n * (1 << 128) < q < n * (1 << 129), "field outside claimed bracket")
    lower = Fraction(m * (p - 2), p - 1)
    margin = (m - 1) ** 2 - 129 * n * 1442 ** 2
    require(lower > m - 1 and margin > 0, "constant comparison failed")
    print(f"p={p}, q={q}, n={n}, u²={a}, exact mean={lower}")
    print(f"forced C > 1442, integer comparison margin={margin}")


if __name__ == "__main__":
    verify_small_field()
    verify_large_anchor()
