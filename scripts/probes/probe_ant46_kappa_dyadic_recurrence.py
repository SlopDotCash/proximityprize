#!/usr/bin/env python3
r"""Exact dyadic audit of the ANT46 canonical kappa polynomial.

For dyadic n >= 4, let K_n(T) be the monic integer polynomial whose roots are

    kappa_n(x) = (x - 1)^n

on the non-self inversion classes in mu_n.  Its degree is n/2 - 1.  If R_n is the
primitive trace polynomial (roots x+x^-1 for primitive n-th roots, modulo inversion), set

    A_2(u) = 2*u + 12,
    A_{2n}(u) = A_n(u)^2 - 2*(u - 2)^n.

The exact recurrence is

    K_{2n}(T) = Sq(K_n)(T) * J_{2n}(T),
    Sq(P)(T) = (-1)^deg(P) P(sqrt(T)) P(-sqrt(T)),
    J_{2n}(T) = Res_u(R_n(u), T^2 + A_n(u)*T + (u - 2)^n),
    R_4(u) = u,                 R_{2n}(u) = R_n(u^2 - 2).

Writing C_n = Disc(K_n)*K_n(2^n), d=deg(K_n), A=Sq(K_n), and J=J_{2n},
the corresponding sufficient-product recurrence is

    C_{2n} = C_n
      * Res(K_n(T),K_n(-T))/(2^d*K_n(0))
      * Disc(J) * Res(A,J)^2
      * (-1)^d*K_n(-2^n)*J(2^(2n)).

Indeed Disc(A)=Disc(K_n)*Res(K_n(T),K_n(-T))/(2^d*K_n(0)) and
A(2^(2n))=(-1)^d*K_n(2^n)*K_n(-2^n).  This is exact, but it exposes four
new states (the plus-resultant, primitive discriminant, cross-resultant, and negative value),
so C_n itself is not closed under doubling.

The first factor contains the old classes and squares their signatures.  The resultant is
the genuinely new primitive half-angle channel.  Pairing traces t and -t proves the formula:
u=t^2-2, the two new signatures are -(t-2)^n and -(t+2)^n, their sum is -A_n(u),
and their product is (u-2)^n.

This probe does five independent exact checks:

* reconstructs K_n from root-of-unity-filtered power sums and Newton identities;
* reconstructs J_{2n} from the odd-root power sums;
* verifies the dyadic factorization and the resultant formula through K_32;
* falsifies the square-only and recycled-K scalar recurrences at K_8, K_16, K_32;
* verifies that Disc(K_n)*K_n(2^n) detects exactly the bad primes <= 500000 for
  n=8,16,32 by an independent finite-field signature computation.

At production n=2^30 the trace/A circuits have 28 doubling steps, but the last primitive
factor still has degree 2^28 and K_n has 2^29 coefficients.  The exact recurrence therefore
gives a succinct *input circuit*, not a logarithmic resultant/nonvanishing certificate.
"""

from __future__ import annotations

from math import comb


LIMIT = 500_000
ORDERS = (8, 16, 32)
PRODUCTION_ORDER = 2**30
FIRST_PRIME = 365375409332725729550921208179070755120141565953
SECOND_PRIME = 730750818665451459101842416358141509841924915201


def trim(poly: list[int]) -> list[int]:
    """Remove leading zeroes from a descending coefficient list."""
    index = 0
    while index + 1 < len(poly) and poly[index] == 0:
        index += 1
    return poly[index:]


def poly_add(left: list[int], right: list[int]) -> list[int]:
    width = max(len(left), len(right))
    left = [0] * (width - len(left)) + left
    right = [0] * (width - len(right)) + right
    return trim([a + b for a, b in zip(left, right, strict=True)])


def poly_scale(poly: list[int], scalar: int) -> list[int]:
    return trim([scalar * value for value in poly])


def poly_mul(left: list[int], right: list[int]) -> list[int]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] += a * b
    return trim(answer)


def poly_pow(poly: list[int], exponent: int) -> list[int]:
    answer = [1]
    base = poly
    while exponent:
        if exponent & 1:
            answer = poly_mul(answer, base)
        base = poly_mul(base, base)
        exponent //= 2
    return answer


def poly_compose(outer: list[int], inner: list[int]) -> list[int]:
    answer = [0]
    for coefficient in outer:
        answer = poly_add(poly_mul(answer, inner), [coefficient])
    return answer


def poly_eval(poly: list[int], value: int, modulus: int | None = None) -> int:
    answer = 0
    for coefficient in poly:
        answer = answer * value + coefficient
        if modulus is not None:
            answer %= modulus
    return answer


def poly_div_exact(dividend: list[int], divisor: list[int]) -> list[int]:
    dividend = dividend[:]
    quotient: list[int] = []
    while len(dividend) >= len(divisor):
        assert dividend[0] % divisor[0] == 0
        leading = dividend[0] // divisor[0]
        quotient.append(leading)
        for index, coefficient in enumerate(divisor):
            dividend[index] -= leading * coefficient
        dividend = trim(dividend)
        if dividend == [0]:
            break
    assert dividend == [0]
    return trim(quotient)


def polynomial_from_power_sums(degree: int, power_sum) -> list[int]:
    """Newton identities for a monic polynomial, returned in descending order."""
    elementary = [1]
    for k in range(1, degree + 1):
        numerator = sum(
            (-1) ** (i - 1) * elementary[k - i] * power_sum(i)
            for i in range(1, k + 1)
        )
        assert numerator % k == 0
        elementary.append(numerator // k)
    return [(-1) ** k * elementary[k] for k in range(degree + 1)]


def canonical_kappa_polynomial(n: int) -> list[int]:
    """K_n from p_r=(n*sum_l binom(nr,nl)-2^(nr))/2."""
    assert n >= 4 and n & (n - 1) == 0

    def power_sum(r: int) -> int:
        filtered = n * sum(comb(n * r, n * ell) for ell in range(r + 1))
        return (filtered - 2 ** (n * r)) // 2

    return polynomial_from_power_sums(n // 2 - 1, power_sum)


def new_primitive_factor(n: int) -> list[int]:
    """J_{2n} from the odd 2n-th roots, one representative per inversion pair."""
    assert n >= 4 and n & (n - 1) == 0

    def power_sum(r: int) -> int:
        alternating = sum(
            (-1) ** ell * comb(2 * n * r, n * ell) for ell in range(2 * r + 1)
        )
        return n * alternating // 2

    return polynomial_from_power_sums(n // 2, power_sum)


def square_signature_transform(poly: list[int]) -> list[int]:
    """Return (-1)^d P(sqrt(T))*P(-sqrt(T))."""
    degree = len(poly) - 1
    in_sqrt = [0] * (2 * degree + 1)  # ascending powers of sqrt(T)
    for i, a in enumerate(poly):
        left_degree = degree - i
        for j, b in enumerate(poly):
            right_degree = degree - j
            in_sqrt[left_degree + right_degree] += a * b * (-1) ** right_degree
    assert all(in_sqrt[index] == 0 for index in range(1, len(in_sqrt), 2))
    ascending = [(-1) ** degree * in_sqrt[2 * index] for index in range(degree + 1)]
    return ascending[::-1]


def negate_argument(poly: list[int]) -> list[int]:
    """P(-T), in descending coefficient order."""
    degree = len(poly) - 1
    return [coefficient * (-1) ** (degree - index) for index, coefficient in enumerate(poly)]


def primitive_trace_polynomial(n: int) -> list[int]:
    """R_4(u)=u and R_{2n}(u)=R_n(u^2-2)."""
    assert n >= 4 and n & (n - 1) == 0
    order = 4
    answer = [1, 0]
    while order < n:
        answer = poly_compose(answer, [1, 0, -2])
        order *= 2
    return answer


def descended_pair_coefficient(n: int) -> list[int]:
    """A_n(u), where u=t^2-2 and A_n=(t-2)^n+(t+2)^n."""
    assert n >= 2 and n & (n - 1) == 0
    order = 2
    answer = [2, 12]
    while order < n:
        answer = poly_add(
            poly_mul(answer, answer),
            poly_scale(poly_pow([1, -2], order), -2),
        )
        order *= 2
    return answer


def bareiss_determinant(matrix: list[list[int]]) -> int:
    matrix = [row[:] for row in matrix]
    size = len(matrix)
    previous = 1
    sign = 1
    for pivot_index in range(size - 1):
        if matrix[pivot_index][pivot_index] == 0:
            swap = next(
                row for row in range(pivot_index + 1, size) if matrix[row][pivot_index]
            )
            matrix[pivot_index], matrix[swap] = matrix[swap], matrix[pivot_index]
            sign = -sign
        pivot = matrix[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (
                    matrix[row][column] * pivot
                    - matrix[row][pivot_index] * matrix[pivot_index][column]
                )
                assert numerator % previous == 0
                matrix[row][column] = numerator // previous
            matrix[row][pivot_index] = 0
        previous = pivot
    return sign * matrix[-1][-1]


def resultant(left: list[int], right: list[int]) -> int:
    left_degree = len(left) - 1
    right_degree = len(right) - 1
    size = left_degree + right_degree
    matrix = []
    for shift in range(right_degree):
        matrix.append([0] * shift + left + [0] * (right_degree - 1 - shift))
    for shift in range(left_degree):
        matrix.append([0] * shift + right + [0] * (left_degree - 1 - shift))
    assert all(len(row) == size for row in matrix)
    return bareiss_determinant(matrix)


def discriminant(poly: list[int]) -> int:
    degree = len(poly) - 1
    derivative = [coefficient * (degree - index) for index, coefficient in enumerate(poly[:-1])]
    return (-1) ** (degree * (degree - 1) // 2) * resultant(poly, derivative)


def resultant_formula_value(n: int, value: int) -> int:
    """Evaluate Res_u(R_n, T^2+A_n*T+(u-2)^n) at T=value."""
    trace = primitive_trace_polynomial(n)
    pair = descended_pair_coefficient(n)
    q = poly_add(
        poly_add(poly_scale(pair, value), [value * value]),
        poly_pow([1, -2], n),
    )
    return resultant(trace, q)


def prime_sieve(limit: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[:2] = b"\x00\x00"
    for divisor in range(2, int(limit**0.5) + 1):
        if is_prime[divisor]:
            start = divisor * divisor
            is_prime[start : limit + 1 : divisor] = b"\x00" * (
                (limit - start) // divisor + 1
            )
    return [value for value in range(2, limit + 1) if is_prime[value]]


def distinct_prime_factors(value: int) -> list[int]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1 if divisor == 2 else 2
    if value > 1:
        factors.append(value)
    return factors


def primitive_root(p: int) -> int:
    factors = distinct_prime_factors(p - 1)
    for candidate in range(2, p):
        if all(pow(candidate, (p - 1) // factor, p) != 1 for factor in factors):
            return candidate
    raise AssertionError(f"no primitive root modulo {p}")


def has_signature_collision(p: int, n: int) -> bool:
    generator = primitive_root(p)
    zeta = pow(generator, (p - 1) // n, p)
    assert pow(zeta, n // 2, p) == p - 1
    seen: set[int] = set()
    self_signature = pow(2, n, p)
    for exponent in range(1, n // 2):
        x = pow(zeta, exponent, p)
        signature = pow((x - 1) % p, n, p)
        if signature == self_signature or signature in seen:
            return True
        seen.add(signature)
    return False


def first_mismatch(left: list[int], right: list[int]) -> tuple[int, int, int]:
    width = max(len(left), len(right))
    left = [0] * (width - len(left)) + left
    right = [0] * (width - len(right)) + right
    for index, (a, b) in enumerate(zip(left, right, strict=True)):
        if a != b:
            return width - 1 - index, a, b
    raise AssertionError("polynomials unexpectedly equal")


def main() -> int:
    print("## Exact K recurrence and falsification")
    canonical = {n: canonical_kappa_polynomial(n) for n in (4, 8, 16, 32)}
    assert canonical[8] == [1, 120, -2160, -256]

    for n in (4, 8, 16):
        target_order = 2 * n
        old = square_signature_transform(canonical[n])
        primitive = new_primitive_factor(n)
        exact = poly_mul(old, primitive)
        assert exact == canonical[target_order]

        # A scalar recurrence that keeps only old classes misses n/2 roots.
        assert old != exact
        # Even recycling K_n and the old self value has the right degree but wrong coefficients.
        recycled = poly_mul(old, poly_mul([1, -(2**n)], canonical[n]))
        assert recycled != exact
        square_witness = first_mismatch(exact, old)
        recycled_witness = first_mismatch(exact, recycled)
        print(
            f"K_{target_order}: degree={len(exact)-1}, old-degree={len(old)-1}, "
            f"new J_{target_order}={primitive}"
        )
        print(
            f"  square-only mismatch (T-degree, exact, naive)={square_witness}; "
            f"recycled-K mismatch={recycled_witness}"
        )

        # Enough integer evaluations to identify the monic resultant polynomial exactly.
        for value in range(len(primitive)):
            assert resultant_formula_value(n, value) == poly_eval(primitive, value)
        print(
            f"  resultant identity checked at {len(primitive)} points "
            f"(degree {len(primitive)-1})"
        )

        # Exact discriminant/self-value recurrence.  Its extra resultants are the state-growth
        # obstruction to iterating only the single scalar C_n.
        degree = len(canonical[n]) - 1
        plus_resultant = resultant(canonical[n], negate_argument(canonical[n]))
        square_disc = discriminant(old)
        square_disc_from_old = (
            discriminant(canonical[n])
            * plus_resultant
            // (2**degree * canonical[n][-1])
        )
        assert square_disc == square_disc_from_old
        cross_resultant = resultant(old, primitive)
        old_certificate = discriminant(canonical[n]) * poly_eval(canonical[n], 2**n)
        target_certificate = discriminant(exact) * poly_eval(exact, 2 ** (2 * n))
        recurrent_certificate = (
            old_certificate
            * (plus_resultant // (2**degree * canonical[n][-1]))
            * discriminant(primitive)
            * cross_resultant**2
            * (-1) ** degree
            * poly_eval(canonical[n], -(2**n))
            * poly_eval(primitive, 2 ** (2 * n))
        )
        assert target_certificate == recurrent_certificate
        print(
            "  C-step exact; auxiliary bit sizes "
            f"plus={abs(plus_resultant).bit_length()}, "
            f"Disc(J)={abs(discriminant(primitive)).bit_length()}, "
            f"cross={abs(cross_resultant).bit_length()}"
        )

    print("\n## Discriminant-times-self certificate versus finite-field collisions")
    primes = prime_sieve(LIMIT)
    for n in ORDERS:
        poly = canonical[n]
        disc = discriminant(poly)
        self_value = poly_eval(poly, 2**n)
        certificate = disc * self_value
        eligible = [p for p in primes if p % n == 1]
        product_bad = [p for p in eligible if certificate % p == 0]
        field_bad = [p for p in eligible if has_signature_collision(p, n)]
        assert product_bad == field_bad
        print(
            f"n={n:2d}: deg={len(poly)-1:2d}, Disc bits={abs(disc).bit_length():4d}, "
            f"K_n(2^n) bits={abs(self_value).bit_length():3d}, bad={field_bad}"
        )

    print("\n## Production arithmetic and complexity boundary")
    degree = PRODUCTION_ORDER // 2 - 1
    pair_count = degree * (degree - 1) // 2
    for label, prime in (("first", FIRST_PRIME), ("second", SECOND_PRIME)):
        assert prime % PRODUCTION_ORDER == 1
        print(
            f"{label} P={prime}; bits={prime.bit_length()}; "
            f"(P-1)/n={(prime-1)//PRODUCTION_ORDER}"
        )
    print(
        f"n={PRODUCTION_ORDER}; deg K_n={degree}; coefficients={degree+1}; "
        f"unordered root pairs={pair_count}"
    )
    print(
        f"Disc Sylvester order={2*degree-1}; final primitive degree={PRODUCTION_ORDER//4}; "
        f"paired-trace degree={PRODUCTION_ORDER//8}; dyadic levels={30-2}"
    )
    print(
        "VERDICT: the exact two-channel recurrence survives, while both tested scalar K_n "
        "recurrences fail.  This recurrence alone is not a logarithmic production certificate: "
        "its succinct R/A circuits feed a resultant whose state width reaches 2^28, so a further "
        "norm-collapse invariant is still required."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
