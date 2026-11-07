#!/usr/bin/env python3
"""Independent recomputation of the zero-membership loci of (x^3, x^2) at t = 3.

This file shares no helper, no engine and no algebraic route with
``probe_t3_zero_membership_locus.py``.  Every conclusion of the primary probe is reached here
through a different derivation, and the two sets of integers are compared literally.

* RESULTANT, three routes.  The primary probe takes ``R_n`` as the determinant of the
  ``n x n`` circulant of multiplication by ``(X+1)^n - 1`` in ``Z[X]/(X^n - 1)``.  Here it is
  recomputed (a) as the ``(2n-1) x (2n-1)`` Sylvester matrix determinant of the two
  polynomials, and (b) as the product over ``d | n`` of the norm of ``(X+1)^n - 1`` in the
  cyclotomic ring ``Z[X]/(Phi_d)`` -- a different factorisation of ``X^n - 1`` into
  ``phi(d) x phi(d)`` multiplication determinants.
* FACTORIZATION, different algorithm.  Pollard-rho with trial division only below ``10^5``,
  the parts re-composed by exact multiplication and every prime factor re-certified prime by
  trial division up to its own square root.
* ZERO-MEMBERSHIP, no resultant and no shape normalisation.  For a prime ``p = 1 (mod n)``
  the bad set is enumerated literally as ``gamma(T) = -D_3(T) * D_2(T)^-1`` over ALL
  ``C(n, 3)`` triples of distinct domain points, ``D_e(T)`` being the 3x3 collinearity
  determinant ``det [[1,1,1],[r1,r2,r3],[r1^e,r2^e,r3^e]]``.  Its cardinality is the census
  count and ``0`` lies in it exactly when ``0`` is bad, so the primary probe's coset keys and
  its Vieta step are re-derived rather than assumed.
* COSET COUNTS, orbit closure.  On a declared ``n = 64`` window the count/coset/zero column is
  recomputed by closing each shape value under multiplication by ``mu_64`` and taking the
  minimum of the orbit as the coset representative -- no exponent key at all.
* SOLUTION COUNTS, polynomial gcd.  ``v_p(R_n)`` is compared with
  ``deg gcd(X^n - 1, (X+1)^n - 1)`` in ``F_p[X]`` at every candidate prime, and that gcd is
  computed to be trivial at declared primes not dividing ``R_n``, including the prize-scale
  Proth primes, where one gcd replaces both a 2^128-scale enumeration and a modular reduction.

Stdlib only, exact integers, no floating point, fixed parameters and a fixed pseudo-random
seed, no timings printed.

Scope.  As in the primary probe: finite prime fields, the single stack ``(x^3, x^2)``,
threshold ``t = 3``, rungs ``n = 8, 16, 32, 64``.  Nothing here is a theorem in ``n`` or ``p``,
a statement about another pencil, about ``t >= 4``, about other bits of the count vector, about
global maxima, about the production regime ``n = 2^30 / 2^32``, about ``delta*``, or about the
prize.
"""

import hashlib
import random
from math import comb, isqrt

RUNGS = (8, 16, 32, 64)
SWEEP_LIMIT = 20_000
N64_WINDOW_LIMIT = 100_000
TRIAL_DIVISION_CUTOFF = 100_000

# Integers quoted from the primary probe's transcript; the comparisons below are literal.
PRIMARY_LOCUS = {
    8: [],
    16: [17],
    32: [97, 193, 257, 353, 449],
    64: [193, 257, 449, 641, 7937, 14657, 15809, 21569, 27457, 33409,
         48449, 63361, 65537, 65921, 204353],
}
PRIMARY_DEGENERATE = {8: [17], 16: [257], 32: [65537], 64: [6700417]}
PRIMARY_R8 = -1343091375
PRIMARY_R16 = -1562716604740038367719196682456673375
PRIMARY_R64_BITS = 1910
PRIMARY_R128_BITS = 7638
PRIMARY_RESIDUAL128_BITS = 2156
PRIMARY_N64_EXTRAS = (193, 257, 449, 641, 7489, 7937, 33409, 39233, 436097,
                      6997057, 6700417)
PRIMARY_WINDOW_DIGEST = (
    "b02413f786a213b06635f3dcd34a97c28593328ed3196a27cae05e6a6e66fb74")
PRIMARY_N8_COUNT = 556
PRIMARY_N8_GENERIC = 40
PRIMARY_N8_EXC = {17: 16}
PRIMARY_N16_COUNT = 279
PRIMARY_N16_GENERIC = 464
PRIMARY_N16_EXC = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
PRIMARY_PRIZE_LADDER = {8: 40, 16: 464, 32: 4512, 64: 39744}


def det_bareiss(matrix):
    size = len(matrix)
    if size == 0:
        return 1
    work = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(size - 1):
        if work[k][k] == 0:
            swap = next((i for i in range(k + 1, size) if work[i][k]), None)
            if swap is None:
                return 0
            work[k], work[swap] = work[swap], work[k]
            sign = -sign
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                work[i][j] = (work[i][j] * work[k][k]
                              - work[i][k] * work[k][j]) // previous
            work[i][k] = 0
        previous = work[k][k]
    return sign * work[size - 1][size - 1]


def poly_divmod(numerator, divisor):
    """Division by a monic polynomial over Z; coefficient lists run low to high."""
    if divisor[-1] != 1:
        raise ValueError("monic divisor required")
    num = numerator[:]
    degree = len(divisor) - 1
    quot = [0] * max(1, len(num) - degree)
    while len(num) - 1 >= degree:
        shift, lead = len(num) - 1 - degree, num[-1]
        quot[shift] = lead
        for i in range(degree + 1):
            num[shift + i] -= lead * divisor[i]
        num.pop()
    while num and num[-1] == 0:
        num.pop()
    return quot, (num or [0])


def is_zero_polynomial(polynomial):
    return not any(polynomial)


def Phi(m):
    """Monic cyclotomic polynomial of index m, from X^m - 1 = prod over d | m of Phi_d."""
    value = [-1] + [0] * (m - 1) + [1]
    for divisor in [d for d in range(1, m) if m % d == 0]:
        value, remainder = poly_divmod(value, Phi(divisor))
        assert is_zero_polynomial(remainder), (m, divisor, remainder)
    return value


def sylvester_resultant(n):
    first = [-1] + [0] * (n - 1) + [1]
    second = [comb(n, k) for k in range(n + 1)]
    second[0] -= 1
    rows = []
    for shift in range(n):
        rows.append([0] * shift + first + [0] * (n - 1 - shift))
    for shift in range(n):
        rows.append([0] * shift + second + [0] * (n - 1 - shift))
    return det_bareiss(rows)


def norm_in_cyclotomic(n, m):
    """Norm of (X+1)^n - 1 in Z[X]/(Phi_m): a phi(m) x phi(m) multiplication determinant."""
    modulus = Phi(m)
    rank = len(modulus) - 1
    element = [comb(n, k) for k in range(n + 1)]
    element[0] -= 1
    _, element = poly_divmod(element, modulus)
    matrix = []
    for i in range(rank):
        _, polynomial = poly_divmod([0] * i + element, modulus)
        matrix.append(polynomial + [0] * (rank - len(polynomial)))
    return det_bareiss(matrix)


def cyclotomic_resultant(n):
    product = 1
    for divisor in [d for d in range(1, n + 1) if n % d == 0]:
        product *= norm_in_cyclotomic(n, divisor)
    return product


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def certify_prime(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def pollard_rho(value):
    rng = random.Random(20261103)
    while True:
        shift = rng.randrange(1, value)
        x = y = rng.randrange(2, value)
        difference = 1
        while difference == 1:
            x = (x * x + shift) % value
            y = (y * y + shift) % value
            y = (y * y + shift) % value
            difference = gcd(abs(x - y), value)
        if difference != value:
            return difference


def split(value, factors):
    if value == 1:
        return
    if value < 10 ** 12:
        divisor = 2
        while divisor * divisor <= value:
            if value % divisor == 0:
                break
            divisor += 1 if divisor == 2 else 2
        if divisor * divisor > value:
            factors[value] = factors.get(value, 0) + 1
            return
        split(divisor, factors)
        split(value // divisor, factors)
        return
    divisor = pollard_rho(value)
    split(divisor, factors)
    split(value // divisor, factors)


def rho_factorization(value):
    rest, factors = abs(value), {}
    for small in [2] + list(range(3, TRIAL_DIVISION_CUTOFF, 2)):
        while rest % small == 0:
            factors[small] = factors.get(small, 0) + 1
            rest //= small
        if small * small > rest:
            break
    if rest > 1:
        split(rest, factors)
    product = 1
    for prime, exponent in sorted(factors.items()):
        assert certify_prime(prime), prime
        product *= prime ** exponent
    assert product == abs(value), (value, factors)
    return factors


def sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if flags[divisor]:
            start = divisor * divisor
            flags[start:limit + 1:divisor] = b"\x00" * len(
                range(start, limit + 1, divisor))
    return flags


def domain(p, n):
    for candidate in range(2, p):
        element = pow(candidate, (p - 1) // n, p)
        if pow(element, n // 2, p) == p - 1:
            values = [pow(element, e, p) for e in range(n)]
            assert len(set(values)) == n
            return values
    raise AssertionError("no element of order %d modulo %d" % (n, p))


def batch_invert(values, p):
    prefix = [1] * (len(values) + 1)
    for index, value in enumerate(values):
        prefix[index + 1] = prefix[index] * value % p
    running = pow(prefix[-1], -1, p)
    out = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        out[index] = running * prefix[index] % p
        running = running * values[index] % p
    return out


def literal_census(p, n):
    """(count, zero flag) of the bad scalars over ALL C(n,3) triples, by determinants."""
    xs = domain(p, n)
    squares = [x * x % p for x in xs]
    cubes = [squares[i] * xs[i] % p for i in range(n)]
    numerators, denominators = [], []
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                a, b, c = xs[i], xs[j], xs[k]
                second = (b * squares[k] - c * squares[j] + c * squares[i]
                          - a * squares[k] + a * squares[j] - b * squares[i]) % p
                third = (b * cubes[k] - c * cubes[j] + c * cubes[i]
                         - a * cubes[k] + a * cubes[j] - b * cubes[i]) % p
                if second:
                    numerators.append(third)
                    denominators.append(second)
    inverses = batch_invert(denominators, p)
    bad = {(-numerators[index] * inverses[index]) % p for index in range(len(numerators))}
    return len(bad), (1 if 0 in bad else 0)


def closure_census(p, n):
    """(count, cosets, zero) with cosets from explicit mu_n orbit closure, no exponent key."""
    xs = domain(p, n)
    representatives, zero = set(), 0
    for i, y in enumerate(xs):
        if y == 1:
            continue
        for z in xs[i + 1:]:
            if z == 1:
                continue
            value = (1 + y + z) % p
            if value == 0:
                zero = 1
                continue
            representatives.add(min((value * w) % p for w in xs))
    return n * len(representatives) + zero, len(representatives), zero


def poly_mod_p(a, b, p):
    a = [c % p for c in a]
    inverse = pow(b[-1], -1, p)
    b = [c * inverse % p for c in b]
    degree = len(b) - 1
    while a and len(a) - 1 >= degree:
        shift, lead = len(a) - 1 - degree, a[-1]
        if lead:
            for i, coefficient in enumerate(b):
                a[shift + i] = (a[shift + i] - lead * coefficient) % p
        while a and a[-1] == 0:
            a.pop()
    return a or [0]


def gcd_degree(p, n):
    a = [(p - 1) % p] + [0] * (n - 1) + [1]
    b = [comb(n, k) % p for k in range(n + 1)]
    b[0] = (b[0] - 1) % p
    while any(b):
        a, b = b, poly_mod_p(a, b, p)
    return max(0, len(a) - 1)


def proth(k, exponent):
    value = k * 2 ** exponent + 1
    assert k % 2 == 1 and k < 2 ** exponent
    witness = 2
    while pow(witness, (value - 1) // 2, value) != value - 1:
        witness += 1
    return value, witness


def main():
    print("crosscheck: independent routes for the (x^3,x^2) t=3 zero-membership loci")
    resultants = {}
    for n in RUNGS:
        sylvester = sylvester_resultant(n)
        cyclotomic = cyclotomic_resultant(n)
        assert sylvester == cyclotomic, (n, sylvester, cyclotomic)
        resultants[n] = sylvester
        quoted = {8: PRIMARY_R8, 16: PRIMARY_R16}.get(n)
        if quoted is not None:
            assert sylvester == quoted, (n, sylvester)
        print("RESULTANT n=%d: the (2n-1)x(2n-1) Sylvester determinant gives %d bits and "
              "the cyclotomic-norm product over the %d divisors of %d gives the same "
              "integer%s; both are independent of the primary probe's circulant route"
              % (n, abs(sylvester).bit_length(),
                 len([d for d in range(1, n + 1) if n % d == 0]), n,
                 ", and equal the quoted primary literal" if quoted is not None else ""))

    locus, degenerate = {}, {}
    for n in RUNGS:
        factors = rho_factorization(resultants[n])
        candidates = sorted(p for p in factors if p > n and p % n == 1)
        hits, dead = [], []
        for p in candidates:
            degree = gcd_degree(p, n)
            count, zero_bad = literal_census(p, n)
            assert degree == factors[p], (n, p, degree, factors[p])
            xs = set(domain(p, n))
            solutions = {a for a in xs if (a + 1) % p in xs}
            assert len(solutions) == degree, (n, p, len(solutions), degree)
            distinct = any(len({1, a, b}) == 3 and (1 + a + b) % p == 0
                           for a in solutions for b in solutions)
            assert distinct == bool(zero_bad), (n, p)
            (hits if zero_bad else dead).append(p)
            if not zero_bad:
                assert solutions == {1 % p, (-2) % p, (-(pow(2, -1, p))) % p}, (n, p)
        locus[n], degenerate[n] = hits, dead
        assert hits == PRIMARY_LOCUS[n], (n, hits, PRIMARY_LOCUS[n])
        assert dead == PRIMARY_DEGENERATE[n], (n, dead, PRIMARY_DEGENERATE[n])
        print("FACTORIZATION n=%d: Pollard-rho after trial division below 10^5 gives %s with every factor "
              "re-certified prime; at all %d candidate primes %s the polynomial-gcd degree "
              "equals v_p(R_%d) and the literal C(%d,3)-triple determinant census puts 0 in "
              "the bad set at %d of them -- reproducing the primary locus %s and the "
              "degenerate-only set %s"
              % (n, "*".join("%d^%d" % (p, e) for p, e in sorted(factors.items())),
                 len(candidates), candidates, n, n, len(hits), hits, dead))
    assert abs(resultants[64]).bit_length() == PRIMARY_R64_BITS
    print("SIZE CHECK: R_64 is %d bits, quoted %d; the primary probe's R_128 is quoted at "
          "%d bits with a %d-bit Fermat-composite residual, which is why the ladder stops "
          "above n = 64" % (abs(resultants[64]).bit_length(), PRIMARY_R64_BITS,
                            PRIMARY_R128_BITS, PRIMARY_RESIDUAL128_BITS))

    flags = sieve(N64_WINDOW_LIMIT)
    primes8 = [p for p in range(8, SWEEP_LIMIT + 1) if flags[p] and p % 8 == 1]
    counts8 = {p: literal_census(p, 8)[0] for p in primes8}
    assert len(primes8) == PRIMARY_N8_COUNT
    assert {p: c for p, c in counts8.items() if c != PRIMARY_N8_GENERIC} == PRIMARY_N8_EXC
    assert all(literal_census(p, 8)[1] == 0 for p in primes8)
    print("MERGED ANCHOR n=8: the raw-triple determinant census reproduces all %d merged "
          "counts (%d everywhere, 16 at p = 17) and puts 0 in no bad set -- the empty locus"
          % (PRIMARY_N8_COUNT, PRIMARY_N8_GENERIC))

    primes16 = [p for p in range(16, SWEEP_LIMIT + 1) if flags[p] and p % 16 == 1]
    counts16, zero16 = {}, []
    for p in primes16:
        count, zero_bad = literal_census(p, 16)
        counts16[p] = count
        if zero_bad:
            zero16.append(p)
    assert len(primes16) == PRIMARY_N16_COUNT
    assert {p: c for p, c in counts16.items() if c != PRIMARY_N16_GENERIC} == PRIMARY_N16_EXC
    assert zero16 == PRIMARY_LOCUS[16], zero16
    print("MERGED ANCHOR n=16: all %d merged counts and the %d-prime exception table "
          "reproduced by the raw route; its [0 bad] column is %s, the primary locus"
          % (PRIMARY_N16_COUNT, len(PRIMARY_N16_EXC), zero16))

    primes32 = [p for p in range(32, SWEEP_LIMIT + 1) if flags[p] and p % 32 == 1]
    zero32 = [p for p in primes32 if literal_census(p, 32)[1]]
    assert zero32 == [p for p in PRIMARY_LOCUS[32] if p <= SWEEP_LIMIT], zero32
    print("n=32 window: %d primes p = 1 (mod 32) in [%d, %d], raw-route [0 bad] at %s (the "
          "n=32 pencil census itself belongs to this campaign's open PR #272)"
          % (len(primes32), primes32[0], SWEEP_LIMIT, zero32))

    primes64 = [p for p in range(64, N64_WINDOW_LIMIT + 1) if flags[p] and p % 64 == 1]
    vector = []
    for p in primes64:
        count, cosets, zero = closure_census(p, 64)
        assert count - zero == 64 * cosets and count <= PRIMARY_PRIZE_LADDER[64], (p, count)
        vector.append("%d,%d,%d,%d;" % (p, count, cosets, zero))
    digest = hashlib.sha256("".join(vector).encode("ascii")).hexdigest()
    zeros = [int(row.split(",")[0]) for row in vector if row.endswith(",1;")]
    assert zeros == [p for p in PRIMARY_LOCUS[64] if p <= N64_WINDOW_LIMIT], zeros
    assert digest == PRIMARY_WINDOW_DIGEST, digest
    print("WINDOW n=64: %d primes p = 1 (mod 64) in [%d, %d] recomputed by mu_64 ORBIT "
          "CLOSURE with minimum-of-orbit coset representatives (no exponent key anywhere); "
          "the window vector digest %s equals the primary probe's exponent-key digest, so "
          "count, coset number and zero bit agree cell by cell by two different algorithms; "
          "zero cells %s"
          % (len(primes64), primes64[0], N64_WINDOW_LIMIT, digest, zeros))

    for p in PRIMARY_N64_EXTRAS:
        count, zero_bad = literal_census(p, 64)
        expected = 1 if p in PRIMARY_LOCUS[64] else 0
        assert zero_bad == expected, (p, zero_bad, expected)
        print("SPOT n=64 p=%d: literal enumeration of all C(64,3) = 41664 triples gives %d "
              "bad scalars and 0 %s a bad scalar, as the locus rule predicts"
              % (p, count, "is" if zero_bad else "is not"))

    for k in (21, 111, 123):
        prize, witness = proth(k, 128)
        for n in RUNGS:
            assert gcd_degree(prize, n) == 0, (k, n)
            assert abs(resultants[n]) % prize != 0, (k, n)
        print("PRIZE p = %d*2^128+1 (Proth witness %d): gcd(X^n-1,(X+1)^n-1) = 1 in F_p[X] "
              "at n = 8, 16, 32, 64, so no vanishing sum exists there at all and 0 is not "
              "bad -- a third route, independent of the determinant of a circulant and of "
              "the direct enumeration" % (k, witness))

    print("PASS: crosscheck reproduces every integer of the primary probe by different "
          "routes -- R_n from the Sylvester matrix and from cyclotomic norms, its complete "
          "factorization from Pollard-rho, v_p(R_n) as a polynomial-gcd degree, 0-membership "
          "from literal C(n,3) determinant enumeration at every candidate prime of every "
          "rung and at every prime of the merged n=8 and n=16 tables, the n=64 window column "
          "from mu_64 orbit closure instead of exponent keys, and the prize-scale verdicts "
          "from trivial gcds; the loci are empty at n=8, {17} at n=16, "
          "{97,193,257,353,449} at n=32 and the primary probe's 15-prime set at n=64, with "
          "degenerate-only primes 17@8, 257@16, 65537@32 and 6700417@64; finite fields only, "
          "this pencil, t=3, no theorem in n or p, no production regime, no delta*, no prize")


if __name__ == "__main__":
    main()
