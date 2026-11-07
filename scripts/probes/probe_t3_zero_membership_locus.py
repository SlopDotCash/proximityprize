#!/usr/bin/env python3
"""Zero-membership loci of the (x^3, x^2) t=3 ceiling census, decided by exact resultants.

Object (the census; the SOURCE of every integer taken as given is stated below).  Fix a
prime ``p = 1 (mod n)``, an element ``g`` of exact
order ``n``, the smooth domain ``mu_n = {g^0, ..., g^(n-1)}`` and the dimension-two code of
affine words ``c0 + c1*x``.  For the stack ``(u0, u1) = (x^3, x^2)`` the ceiling (``t = 3``)
bad scalars are the ``gamma`` for which ``x^3 + gamma*x^2`` agrees with an affine word on
some triple ``T`` while ``(x^3, x^2)`` is not jointly affine on ``T``.  Those per-prime count
tables are merged at ``n = 8`` and ``n = 16`` (``probe_order16_weight13_spectrum.py``,
PR #264, and ``probe_n16_below_ceiling_max.py``, PR #267), and the structural law
``count = n * cosets + [0 bad]`` is recorded at ``n = 64`` only by this campaign's STAGED,
UNSUBMITTED p-scaling probe, not by merged code.

The single bit ``[0 bad]`` is the object here, and two exact routes meet on it.

* Census route.  ``gamma = -D_3(T)/D_2(T)`` in the collinearity determinants, so ``0`` is
  bad iff some triple has ``D_3(T) = 0`` (and ``D_2(T) != 0``, which is automatic for three
  distinct points because a quadratic has at most two roots).  ``D_3(T) = 0`` says the three
  values ``r^3`` are affine on ``T``, i.e. ``T`` is the full root set of a monic cubic
  ``X^3 - b*X - a`` whose ``X^2`` coefficient is ``0``, so Vieta gives ``r1 + r2 + r3 = 0``.
  Dilating ``T`` by an element of ``mu_n`` preserves vanishing of the sum, hence
  ``0 bad  <=>  there exist pairwise distinct 1, a, b in mu_n with 1 + a + b = 0``.
* Divisibility route.  With ``R_n = Res(X^n - 1, (X+1)^n - 1)``, and ``p = 1 (mod n)`` so
  ``X^n - 1`` splits into ``n`` distinct linear factors over ``F_p``,
  ``R_n = prod_{a in mu_n} ((a+1)^n - 1)`` evaluated in ``F_p``; so a vanishing sum exists,
  not necessarily with distinct elements, iff ``p`` divides ``R_n``.  ``n`` is even, so
  ``-1 in mu_n`` and the sign is immaterial.

What this probe certifies, by exact integer arithmetic only:

1. Complete factorizations: ``R_8 = -3^7*5^3*17^3`` (31 bits),
   ``R_16 = -3^7*5^3*7^6*17^15*257^3`` (121 bits),
   ``R_32 = -3^7*5^3*7^6*17^15*47^6*97^12*193^6*257^9*353^6*449^6*65537^3`` (478 bits) and
   the 1910-bit / 575-digit ``R_64`` -- each with residual cofactor exactly ``1``.  Both bit
   sizes are those of the staged, unsubmitted lane and are re-derived and asserted here.
   ``R_128`` is recomputed at the staged lane's 7638 bits and leaves a composite cofactor, so the
   procedure stops below that rung.
2. Because those four factorizations are complete, the zero-membership set is FINITE and
   listed for EVERY prime of the class, not only for a swept window: ``n = 8``: empty;
   ``n = 16``: ``{17}``; ``n = 32``: ``{97, 193, 257, 353, 449}``; ``n = 64``: the 15-prime
   set ending at ``204353``.
3. Degeneracy decided prime by prime: among the primes ``p = 1 (mod n)`` dividing ``R_n``,
   exactly ``17`` (at ``n = 8``), ``257`` (at ``n = 16``), ``65537`` (at ``n = 32``) and
   ``6700417`` (at ``n = 64``) carry no distinct solution, and each of their solution sets is
   exhibited to be exactly the three forced degenerate ones ``{1, -2, -1/2}``.
4. Exponent law: at every candidate prime of every rung, ``v_p(R_n)`` equals the number of
   ``a in mu_n`` with ``a + 1 in mu_n``.
5. Inheritance: ``R_8 | R_16 | R_32 | R_64 | R_128`` by exact division, with quotient sizes.
6. Census tie-out: the merged ``n = 8`` table (556 primes, ``40`` except ``17: 16``) and the
   merged ``n = 16`` table (279 primes, ``464`` outside the published 34-prime exception set)
   are reproduced cell by cell together with their ``[0 bad]`` column, the merged exception
   value at ``17: 17`` is the unique merged count congruent to ``1`` modulo ``16``, and the
   ``n = 64`` sweep of all 14896 primes ``p = 1 (mod 64)`` in ``[193, 7000000]`` reproduces
   the staged profile digest, the ``8430/6466`` ceiling split, the first ceiling cell, the
   largest below-ceiling cell and the 15 zero cells.
7. Prize-scale decision without enumeration at 2^128 scale: at the Proth primes
   ``k*2^128 + 1``, ``k = 21, 111, 123``, every ``R_n`` is nonzero modulo ``p``, so ``0`` is
   not bad there; the same 12 cells are also decided by direct pair enumeration at those
   primes and the two routes agree.  Hence the counts recorded for those primes are exact
   multiples of ``n`` (the merged ``40``, and the ``464 / 4512 / 39744`` ladder of this
   campaign's open PRs #272/#300/#341).

Engine.  ``R_n`` is the determinant of the circulant ``mult`` by ``(X+1)^n - 1`` in
``Z[X]/(X^n - 1)``, computed by fraction-free Bareiss elimination over the integers;
factorisation is trial division; coset keys are ``gamma^n mod p`` with no discrete
logarithm; triples and pairs are enumerated directly.  No floating point, no randomness,
fixed parameters, and no stage timings are printed, so transcripts are byte-identical
across runs by construction.

Scope (read before citing).  Finite prime fields; the single monomial stack ``(x^3, x^2)``;
threshold ``t = 3`` only; rungs ``n = 8, 16, 32, 64``, with ``n = 128`` touched only to locate
where the method stops.  The per-rung classification is a computed fact about that rung's
integer ``R_n`` together with the elementary Vieta/common-root equivalences stated above,
which are verified here at every cell examined; it is not a Lean theorem, not a statement
about any other pencil, about ``t >= 4``, about the remaining bits of the count vector, about
global maxima, about the production regime ``n = 2^30 / 2^32``, about ``delta*``, and about
the prize.
"""

import hashlib
from itertools import combinations
from math import comb, isqrt

RUNGS = (8, 16, 32, 64)
SWEEP_LIMIT = 20_000
N64_LIMIT = 7_000_000
PRIZE_EXPONENT = 128
PRIZE_KS = (21, 111, 123)
TRIAL_DIVISION_CUTOFF = 100_000_000

# Merged in-tree integers (PR #264 G330 boundary at n=8, PR #267 at n=16).
N8_COUNT = 556
N8_GENERIC = 40
N8_EXC = {17: 16}
N16_COUNT = 279
N16_GENERIC = 464
N16_EXC = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}

# Published sizes and the n=64 locus/profile integers from this campaign (staged p-scaling
# probe; the ceiling value 39744 is the open-PR #300/#341 prize-scale integer).
R64_BITS = 1910
R128_BITS = 7638
N64_CANDIDATES = (193, 257, 449, 641, 7937, 14657, 15809, 21569, 27457, 33409,
                  48449, 63361, 65537, 65921, 204353, 6700417)
N64_ZERO_LOCUS = (193, 257, 449, 641, 7937, 14657, 15809, 21569, 27457, 33409,
                  48449, 63361, 65537, 65921, 204353)
N64_PRIMES = 14896
N64_CEILING = 39744
N64_AT_CEILING = 8430
N64_BELOW_CEILING = 6466
N64_FIRST_CEILING = 436097
N64_LARGEST_BELOW = 6997057
N64_DIGEST = "24ecf8668f759e6f76443f32f58f4ececdf0db886969de620c75eefed6350878"
PRIZE_LADDER = ((16, 464), (32, 4512), (64, 39744))

EXPECTED_LOCUS = {8: [], 16: [17], 32: [97, 193, 257, 353, 449], 64: list(N64_ZERO_LOCUS)}
EXPECTED_DEGENERATE = {8: [17], 16: [257], 32: [65537], 64: [6700417]}


def bareiss_det(matrix):
    size = len(matrix)
    work = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for k in range(size - 1):
        if work[k][k] == 0:
            pivot = next((i for i in range(k + 1, size) if work[i][k]), None)
            if pivot is None:
                return 0
            work[k], work[pivot] = work[pivot], work[k]
            sign = -sign
        pivot_value = work[k][k]
        pivot_row = work[k]
        for i in range(k + 1, size):
            row = work[i]
            factor = row[k]
            for j in range(k + 1, size):
                row[j] = (row[j] * pivot_value - factor * pivot_row[j]) // previous
            row[k] = 0
        previous = pivot_value
    return sign * work[size - 1][size - 1]


def resultant(n):
    """Res(X^n-1, (X+1)^n-1): the circulant of multiplication by (X+1)^n-1 mod X^n-1."""
    row = [1] + [comb(n, k) for k in range(1, n)]
    return bareiss_det([[row[(j - i) % n] for j in range(n)] for i in range(n)])


def is_prime(value):
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


def factor_by_trial_division(value, cutoff=None):
    """Prime powers below the cutoff, plus the untouched residual."""
    rest = abs(value)
    factors = []
    divisor = 2
    limit = cutoff if cutoff is not None else rest
    while divisor * divisor <= rest and divisor <= limit:
        if rest % divisor == 0:
            exponent = 0
            while rest % divisor == 0:
                rest //= divisor
                exponent += 1
            factors.append((divisor, exponent))
        divisor += 1 if divisor == 2 else 2
    product = 1
    for prime, exponent in factors:
        assert is_prime(prime), prime
        product *= prime ** exponent
    assert product * rest == abs(value), (value, factors, rest)
    return factors, rest


def sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if flags[divisor]:
            start = divisor * divisor
            flags[start:limit + 1:divisor] = b"\x00" * len(
                range(start, limit + 1, divisor))
    return flags


def primes_one_mod(p_mod, limit, flags):
    return [p for p in range(p_mod, limit + 1) if flags[p] and p % p_mod == 1]


def proth_prime(k, exponent):
    value = k * 2 ** exponent + 1
    assert k % 2 == 1 and k < 2 ** exponent
    witness = 2
    while pow(witness, (value - 1) // 2, value) != value - 1:
        witness += 1
    return value, witness


def order_element(p, n):
    for candidate in range(2, p):
        element = pow(candidate, (p - 1) // n, p)
        if pow(element, n // 2, p) == p - 1:
            assert pow(element, n, p) == 1 and element != 1
            return element
    raise AssertionError("no element of order %d modulo %d" % (n, p))


def mu(p, n):
    generator = order_element(p, n)
    values = [pow(generator, e, p) for e in range(n)]
    assert len(set(values)) == n and values[0] == 1
    assert p - 1 in values, "-1 must lie in mu_n for even n"
    return values


def census(p, n):
    """(count, cosets, zero) for the (x^3, x^2) t=3 bad scalars, through coset keys."""
    keys = set()
    zero = 0
    for y, z in combinations(sorted(mu(p, n))[1:], 2):
        ratio = (1 + y + z) % p
        if ratio == 0:
            zero = 1
        else:
            keys.add(pow(ratio, n, p))
    return n * len(keys) + zero, len(keys), zero


def root_product_mod_p(p, n):
    """prod over a in mu_n of ((a+1)^n - 1), i.e. the resultant evaluated in F_p."""
    product = 1
    for a in mu(p, n):
        product = product * (pow((a + 1) % p, n, p) - 1) % p
    return product


def solution_set(p, n):
    xs = set(mu(p, n))
    return sorted(a for a in xs if (a + 1) % p in xs)


def forced_degenerates(p):
    """The three solutions of 1 + a + b = 0 that never give a DISTINCT triple."""
    return {1 % p, (-2) % p, (-(pow(2, -1, p))) % p}


def main():
    print("t=3 ceiling zero-membership loci of (x^3,x^2), decided by "
          "R_n = Res(X^n-1,(X+1)^n-1)")
    print("rungs n = %s; primes p = 1 (mod n); domain mu_n; threshold t = 3; pencil (3,2)"
          % ", ".join(str(r) for r in RUNGS))
    flags = sieve(N64_LIMIT)
    prizes = {}
    for k in PRIZE_KS:
        prizes[k], witness = proth_prime(k, PRIZE_EXPONENT)
        print("primality: primes <= %d by sieve; p = %d*2^%d+1 is prime by Proth's theorem "
              "with witness a = %d" % (N64_LIMIT, k, PRIZE_EXPONENT, witness))

    # 1. Merged census tables reproduced cell by cell, with the new [0 bad] column.
    sweep_loci = {}
    for n in (8, 16):
        count_expected, generic, exc = ((N8_COUNT, N8_GENERIC, N8_EXC) if n == 8
                                        else (N16_COUNT, N16_GENERIC, N16_EXC))
        primes = primes_one_mod(n, SWEEP_LIMIT, flags)
        assert len(primes) == count_expected, (n, len(primes))
        table, zeros = {}, []
        for p in primes:
            count, cosets, zero = census(p, n)
            assert count - zero == n * cosets, (n, p, count, zero)
            table[p] = count
            if zero:
                zeros.append(p)
        exceptional = {p: c for p, c in table.items() if c != generic}
        assert exceptional == exc, (n, sorted(exceptional.items()))
        multiples = sorted(p for p, c in table.items() if c % n != 0)
        assert multiples == zeros, (n, multiples, zeros)
        if n == 16:
            assert zeros == [17], zeros
        sweep_loci[n] = zeros
        assert zeros == [p for p in primes if p in EXPECTED_LOCUS[n]], (n, zeros)
        print("merged anchor n=%d: %d primes p = 1 (mod %d) in [%d, %d], count %d at %d of "
              "them and the other %d == merged PR #267 exception table; new [0 bad] column "
              "is %s; the only merged count congruent to 1 mod 16 is 17: 17" %
              (n, len(primes), n, primes[0], SWEEP_LIMIT, generic,
               len(primes) - len(exceptional), len(exceptional),
               "empty" if not zeros else str(zeros)))
    primes32 = primes_one_mod(32, SWEEP_LIMIT, flags)
    sweep_loci[32] = [p for p in primes32 if census(p, 32)[2]]
    assert sweep_loci[32] == [p for p in primes32 if p in EXPECTED_LOCUS[32]]
    print("n=32 swept window [%d, %d]: %d primes, [0 bad] at %s (the n=32 PENCIL census is "
          "this campaign's open PR #272; only the zero bit is claimed here)"
          % (primes32[0], SWEEP_LIMIT, len(primes32), sweep_loci[32]))

    # 2. Complete factorizations, the exponent law, degeneracy, and the finite loci.
    resultants, factorizations = {}, {}
    loci, degenerate_only = {}, {}
    for n in RUNGS:
        value = resultants.setdefault(n, resultant(n))
        assert value < 0, (n, value)
        factors, residual = factor_by_trial_division(value)
        assert residual == 1, (n, residual)
        factorizations[n] = factors
        exponent = dict(factors)
        candidates = sorted(p for p, _ in factors if p > n and p % n == 1)
        hits, degenerate = [], []
        for p in candidates:
            solutions = solution_set(p, n)
            assert len(solutions) == exponent[p], (n, p, len(solutions), exponent[p])
            assert root_product_mod_p(p, n) == 0, (n, p)
            assert all(a in mu(p, n) and (a + 1) % p in mu(p, n) for a in solutions)
            if set(solutions) == forced_degenerates(p):
                assert census(p, n)[2] == 0, (n, p)
                degenerate.append(p)
            else:
                assert census(p, n)[2] == 1, (n, p)
                hits.append(p)
        assert [p for p in sweep_loci.get(n, []) if p not in hits] == []
        loci[n], degenerate_only[n] = hits, degenerate
        assert hits == EXPECTED_LOCUS[n], (n, hits, EXPECTED_LOCUS[n])
        assert degenerate == EXPECTED_DEGENERATE[n], (n, degenerate)
        print("R_%d = -%s (%d bits, residual cofactor 1: COMPLETE factorization); primes "
              "p = 1 (mod %d) dividing it: %d of them %s; v_p(R_%d) = #solutions at every "
              "one of them; degenerate-only (solution set exactly {1, -2, -1/2}): %s"
              % (n, "*".join("%d^%d" % (p, e) for p, e in factors),
                 abs(value).bit_length(), n, len(candidates), candidates, n,
                 degenerate))
    assert abs(resultants[64]).bit_length() == R64_BITS, resultants[64].bit_length()
    assert [p for p, _ in factorizations[64] if p > 64 and p % 64 == 1] == list(N64_CANDIDATES)

    r128 = resultant(128)
    _, residual128 = factor_by_trial_division(r128, cutoff=TRIAL_DIVISION_CUTOFF)
    assert abs(r128).bit_length() == R128_BITS, r128.bit_length()
    assert residual128 > 1
    assert pow(2, residual128 - 1, residual128) != 1, "Fermat compositeness certificate"
    print("R_128 = %d bits == staged (unsubmitted) lane size; trial division below %d leaves a residual of "
          "%d bits which fails the Fermat test (2^(q-1) != 1 mod q), so it is composite and "
          "the factorization is NOT complete: at n = 128 this decision procedure cannot list "
          "the locus" % (abs(r128).bit_length(), TRIAL_DIVISION_CUTOFF,
                         residual128.bit_length()))

    # 3. The loci hold over every prime of the class, not only over swept windows.
    for n in RUNGS:
        print("LOCUS n=%d: for EVERY prime p = 1 (mod %d), 0 is a bad scalar of (x^3,x^2) at "
              "t = 3 on mu_%d iff p is in %s -- %d prime(s), complete because R_%d is fully "
              "factored" % (n, n, n, loci[n] if loci[n] else "{} (empty locus)",
                            len(loci[n]), n))
    for n in (8, 16, 32):
        deeper = [p for p, _ in factorizations[n] if p > n and p % (2 * n) == 1]
        assert all(p in [q for q, _ in factorizations[2 * n]] for p in deeper), (n, deeper)
        assert [p for p in loci[n] if p % (2 * n) == 1] == \
            [p for p in loci[n] if p % (2 * n) == 1 and p in loci[2 * n]], (n,)
        gained = [p for p in deeper if p not in loci[n] and p in loci[2 * n]]
        print("locus inheritance at the step %d -> %d: the %d R_%d candidates that are also "
              "1 (mod %d) are %s, all of which divide R_%d; the degenerate-only primes "
              "%s that become distinct-locus members at mu_%d are %s"
              % (n, 2 * n, len(deeper), n, 2 * n, deeper, 2 * n,
                 degenerate_only[n], 2 * n, gained))

    # 4. Inheritance along the 2-power ladder.
    for n in (8, 16, 32, 64):
        upper = resultants[n * 2] if n * 2 in resultants else r128
        quotient, remainder = divmod(upper, resultants[n])
        assert remainder == 0, n
        print("inheritance: R_%d divides R_%d exactly (quotient %d bits), so every vanishing "
              "sum in mu_%d is one in mu_%d" % (n, n * 2, quotient.bit_length(), n, n * 2))

    # 5. The staged (unsubmitted) n=64 sweep, reproduced through this engine in one pass.
    primes64 = primes_one_mod(64, N64_LIMIT, flags)
    assert len(primes64) == N64_PRIMES, len(primes64)
    vector, zeros64, at_ceiling = [], [], 0
    first_ceiling, largest_below = None, None
    for p in primes64:
        count, cosets, zero = census(p, 64)
        assert count - zero == 64 * cosets and count <= N64_CEILING, (p, count)
        vector.append("%d,%d,%d,%d;" % (p, count, cosets, zero))
        if count == N64_CEILING:
            at_ceiling += 1
            if first_ceiling is None:
                first_ceiling = p
        else:
            largest_below = p
        if zero:
            zeros64.append(p)
    digest = hashlib.sha256("".join(vector).encode("ascii")).hexdigest()
    window = [row for row in vector if int(row.split(",")[0]) <= 100_000]
    window_digest = hashlib.sha256("".join(window).encode("ascii")).hexdigest()
    assert digest == N64_DIGEST, digest
    assert zeros64 == list(N64_ZERO_LOCUS), zeros64
    assert (at_ceiling, len(primes64) - at_ceiling) == (N64_AT_CEILING, N64_BELOW_CEILING)
    assert (first_ceiling, largest_below) == (N64_FIRST_CEILING, N64_LARGEST_BELOW)
    print("n=64 window digest over the %d cells with p <= 100000: %s"
          % (len(window), window_digest))
    print("n=64 sweep: %d primes p = 1 (mod 64) in [193, %d] reproduce the staged profile "
          "vector digest %s, count == %d at %d cells and below it at %d, first ceiling cell "
          "p = %d, largest below-ceiling cell p = %d, and [0 bad] at exactly the %d-prime "
          "locus of section 2" % (len(primes64), N64_LIMIT, digest, N64_CEILING, at_ceiling,
                                  len(primes64) - at_ceiling, first_ceiling, largest_below,
                                  len(zeros64)))

    # 6. Prize-scale cells, decided by modular reduction and by direct enumeration.
    for n in RUNGS:
        for k in PRIZE_KS:
            p = prizes[k]
            divides = resultants[n] % p == 0
            shapes = [(y, z) for y, z in combinations(sorted(set(mu(p, n)))[1:], 2)]
            enumerated = any((1 + y + z) % p == 0 for y, z in shapes)
            assert not divides and not enumerated, (n, k, divides, enumerated)
            assert root_product_mod_p(p, n) != 0, (n, k)
            print("prize decision n=%d, p = %d*2^128+1: R_%d mod p != 0, and direct "
                  "enumeration of the %d normalised shapes {1,y,z} over mu_%d at that prime "
                  "finds no vanishing sum -- both routes say 0 is NOT bad, so its count is a "
                  "multiple of %d" % (n, k, n, len(shapes), n, n))
    assert N8_GENERIC % 8 == 0 and all(c % n == 0 for n, c in PRIZE_LADDER)
    print("consistency: the merged count 40 at n=8 and the prize ladder 464 / 4512 / 39744 "
          "(open PRs #272/#300/#341, not merged) are multiples of n, as an absent zero bit "
          "requires; at n=16 the merged exception value 17 = 16*1 + 1 is the one cell whose "
          "count is not a multiple of n, and 17 is exactly the n=16 locus")

    print("PASS: exact zero-membership of the (x^3,x^2) t=3 ceiling census at n = 8, 16, 32, "
          "64 decided for EVERY prime p = 1 (mod n), because R_8 = -3^7*5^3*17^3, "
          "R_16 = -3^7*5^3*7^6*17^15*257^3, R_32 (478 bits) and the 1910-bit R_64 "
          "factor completely: the loci are empty at n=8, {17} at n=16, "
          "{97,193,257,353,449} at n=32 and the 15-prime set ending at 204353 at n=64; "
          "v_p(R_n) = #solutions at every candidate, the degenerate-only primes are 17@8, "
          "257@16, 65537@32 and 6700417@64, R_n divides R_2n up to R_128, R_128 leaves a "
          "Fermat-composite residual so the method stops below that rung, the merged n=8 and "
          "n=16 tables and the 14896-cell n=64 profile digest are reproduced, and 0 is not "
          "bad at the three prize-scale Proth primes by both the modular and the enumeration "
          "route; no theorem in n or p, no other pencil, no t>=4, no other bit of the count "
          "vector, no global maximum, no production regime, no delta* and no prize claim")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
