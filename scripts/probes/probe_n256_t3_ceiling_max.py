#!/usr/bin/env python3
"""Exact n=256 ceiling (t=3) monomial-pencil maximum census at the prize-scale prime.

Object.  Fix a prime ``p = 1 (mod n)``, a generator ``g`` of order ``n = 256`` in
``F_p``, the smooth domain ``x_i = g^i``, and the dimension-two code of affine
words ``c0 + c1*x``.  For the monomial pencil ``(u0, u1) = (x^a, x^b)`` the
*ceiling* bad scalars are the gammas for which ``u0 + gamma*u1`` agrees with an
affine word on some triple ``S`` (``|S| >= 3``) while ``(u0, u1)`` is not
jointly affine on ``S`` (the ``pairJointAgreesOn`` exclusion of the repository
MCA event).  This probe censuses the t = 3 ceiling count over all ``n^2``
ordered monomial pencils, for every rung ``n = 8, 16, 32, 64, 128`` and the new
rung ``n = 256``, all at the prize-scale Proth prime ``p = 21*2^128 + 1``.

Exact characterisation (same as the published rungs).  With ``D_e(T)`` the
collinearity determinant of ``(x_i, x_i^e)`` on the triple ``T``, the triple
condition is linear in gamma and the bad set is exactly
``{ -D_a(T)/D_b(T) : D_b(T) != 0 }``.  Writing ``D_e = V_T * h_{e-2}`` (``V_T``
the Vandermonde product, ``h`` the complete homogeneous polynomial) gives the
ratio through the closed form
``h_k(1,y,z) = ((y-z) + y^{k+2}(z-1) + z^{k+2}(1-y)) / ((1-y)(1-z)(y-z))``.
Scaling a triple by ``g`` multiplies the ratio by ``g^{a-b}``, so with
``m = n/gcd((b-a) mod n, n)`` the bad set is a union of cosets of the order-``m``
subgroup and the count is ``m * (#nonzero cosets) + [0 is bad]``.

Fast evaluation of that count.  The coset key of a ratio ``v`` is ``v^m``.
Because ``m`` is a power of two and ``m >= 2`` for every off-diagonal pencil,
``v^m = phi_a(s)^m / phi_b(s)^m`` (the sign ``(-1)^m`` is one), where
``phi_e(s) = h_{e-2}(1,y_s,z_s)``.  Precomputing the table ``phi^m`` for one
2-adic class at a time (the table for ``m`` is the previous table squared)
removes the per-shape modular exponentiation.  This is an exact identity, not
an approximation; the companion crosscheck recomputes the same integers with
the plain per-shape power and a literal triple enumeration.

New rung (the claim of this probe).  At ``p = 21*2^128 + 1`` the t = 3 ceiling
count over all 65536 monomial pencils on ``mu_256`` has maximum
``2746624 = C(256,3) - 256*(256/4 + 2)``, attained at exactly 3584 pencils; the
``(3,2)`` pencil has count ``2731264``; the four quadratic-character pencils
``(128,127), (128,255), (129,2), (129,130)`` have count ``532481``.  The full
count vector is pinned by the two checksums and the winner digest below.

Observed pattern (finite data, not a theorem in n).  Together with the
published rungs this gives, at the tested prize-scale primes,

    t=3 maximum = C(n,3) - n*(n/4 + 2)   for n = 16, 32, 64, 128, 256
                = 464, 4640, 40512, 337024, 2746624,

while the n=8 cell (max 40) does not follow it.  No claim is made that this
formula persists at the production n = 2^30/2^32.

Scope (read before citing).  Finite fields only; the smooth domain ``mu_256``;
dimension-two affine code; monomial pencils only -- this is **not** a maximum
over arbitrary word pairs or stacks.  Only the four listed prize-scale Proth
primes are covered, and the n=256 full census is run at ``k = 21`` only; the
other two primes are checked on the listed pencils, not by a full census.
``n = 256`` is still far below the production ``n = 2^30/2^32``; nothing here
is a production-regime statement, a ``delta*`` claim, or a step toward the
prize.  Stdlib only, deterministic, integer arithmetic only.
"""

import time
from math import gcd

PRIZE_EXP = 128
PRIZE_K = 21
EXTRA_PRIZE = ((111, 5), (123, 7))

# Published n=8 ceiling cells and winners.
N8_CELLS = {41: 40, 257: 40}
N8_WINNERS = ((2, 3), (3, 2), (6, 7), (7, 6))

# Published n=16, n=32, n=64 ceiling integers (PR #264, PR #272, held t=3 lane).
N16_PRIZE_MAX = 464
N32_PRIZE_MAX = 4640
N32_PRIZE_WINNER_COUNT = 56
N32_PRIZE_STACK = 4512
N64_PRIZE_MAX = 40512
N64_PRIZE_WINNER_COUNT = 224
N64_PRIZE_STACK = 39744
N64_PRIZE_SUM = 96271090
N64_PRIZE_WEIGHTED = 203372423673

# Held n=128 t=3 lane integers, reproduced through this code path.
N128_MAX = 337024
N128_WINNER_COUNT = 896
N128_STACK = 333440
N128_SUM = 3435426354
N128_WEIGHTED = 28584462914073
N128_WINNER_WEIGHTED = 7455168
N128_FIRST_WINNERS = ((2, 11), (2, 19), (2, 27), (2, 43), (2, 51),
                      (2, 59), (2, 75), (2, 83), (2, 91), (2, 107))

# New n=256 rung (hard-asserted on every run).
N256_MAX = 2746624
N256_WINNER_COUNT = 3584
N256_STACK = 2731264
N256_SUM = 115947536562
N256_WEIGHTED = 3829109404545625
N256_WINNER_WEIGHTED = 118359808
N256_FIRST_WINNERS = ((2, 11), (2, 19), (2, 27), (2, 43), (2, 51),
                      (2, 59), (2, 75), (2, 83), (2, 91), (2, 107),
                      (2, 115), (2, 123), (2, 139), (2, 147), (2, 155),
                      (2, 171))
N256_CHAR_PENCILS = ((128, 127), (128, 255), (129, 2), (129, 130))
N256_CHAR_COUNT = 532481
N256_MULTI_PRIZE_SPOT = ((3, 2), (2, 11), (2, 19), (2, 27), (2, 43),
                         (128, 127), (128, 255), (129, 2), (129, 130))


def order_element(p, n):
    if (p - 1) % n:
        raise AssertionError(f"{n} does not divide p-1 for p={p}")
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def batch_inverse(values, p):
    prefix = [1] * (len(values) + 1)
    for index, value in enumerate(values):
        prefix[index + 1] = prefix[index] * (value if value else 1) % p
    inverse = pow(prefix[-1], -1, p)
    out = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        value = values[index]
        if value:
            out[index] = inverse * prefix[index] % p
            inverse = inverse * value % p
    return out


def shape_phi(n, p):
    """phi[e][slot] = h_{e-2}(1, y, z) for the triple shape {0, y, z}."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
    denom = [((1 - xs[u]) * (1 - xs[v]) * (xs[u] - xs[v])) % p for u, v in pairs]
    inverse_denom = batch_inverse(denom, p)
    phi = [[0] * len(pairs) for _ in range(n)]
    for slot, (u, v) in enumerate(pairs):
        y, z = xs[u], xs[v]
        inverse = inverse_denom[slot]
        y_power, z_power = 1, 1
        for exponent in range(n):
            numerator = ((y - z) + y_power * (z - 1) + z_power * (1 - y)) % p
            phi[exponent][slot] = numerator * inverse % p
            y_power = y_power * y % p
            z_power = z_power * z % p
    # h_{-2} = h_{-1} = 0 and h_0 = 1 on every shape.
    assert not any(phi[0]) and not any(phi[1])
    assert all(value == 1 for value in phi[2])
    return phi


def square_table(table, p):
    return [[value * value % p for value in row] for row in table]


def census(n, p):
    """Exact t=3 ceiling counts for all n^2 ordered pencils.

    For a pencil with m = n/gcd(b-a, n) >= 2 the coset key of the ratio
    -phi_a/phi_b is phi_a^m/phi_b^m, so the table phi^m (built by repeated
    squaring, one table per 2-adic class) yields the same set of nonzero keys
    as the plain per-shape power.  m = 1 happens only for a = b; there the
    engine keeps the plain ratio and the count is 0 or 1, immaterial for the
    maximum.
    """
    rows = len(phi_rows)
    slots = len(phi_rows[0])
    counts = {}
    table = phi_rows
    k = 1
    while True:
        g = n // k
        for b in range(rows):
            row_b = table[b]
            inverse_b = batch_inverse(row_b, p)
            for a in range(rows):
                if gcd((b - a) % n, n) != g:
                    continue
                row_a = table[a]
                seen = set()
                add = seen.add
                for slot in range(slots):
                    q = row_b[slot]
                    if q:
                        add(row_a[slot] * inverse_b[slot] % p)
                zero = 0 in seen
                counts[a * n + b] = (k * (len(seen) - (1 if zero else 0))
                                     + (1 if zero else 0))
        if k == n:
            break
        table = square_table(table, p)
        k *= 2
    assert len(counts) == n * n
    return counts


def summarize(counts, n):
    maximum = max(counts.values())
    winners = sorted(divmod(code, n) for code, count in counts.items()
                     if count == maximum)
    return maximum, winners


def checksums(counts, n):
    total = 0
    weighted = 0
    for code, count in counts.items():
        a, b = divmod(code, n)
        total += count
        weighted += count * (a * n + b)
    return total, weighted


def plain_count(n, p, phi, inverse_phi, a, b):
    """One pencil through the plain per-shape power (used for spot checks)."""
    phi_a, phi_b = phi[a], phi[b]
    inverse_b = inverse_phi[b]
    m = n // gcd((b - a) % n, n)
    seen = set()
    add = seen.add
    for slot in range(len(phi_a)):
        if phi_b[slot]:
            value = (-phi_a[slot] * inverse_b[slot]) % p
            if m == 1:
                add(value)
            elif m == 2:
                add(value * value % p)
            else:
                add(pow(value, m, p))
    zero = 0 in seen
    return m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)


def prize_prime(k=21):
    p = k * (2 ** PRIZE_EXP) + 1
    witness = 5 if k in (21, 111) else 7
    assert k < 2 ** PRIZE_EXP
    assert pow(witness, (p - 1) // 2, p) == p - 1, k
    return p


phi_rows = []


def main():
    global phi_rows
    start = time.time()

    for p, expected in N8_CELLS.items():
        phi_rows = shape_phi(8, p)
        counts = census(8, p)
        maximum, winners = summarize(counts, 8)
        assert (maximum, tuple(winners)) == (expected, N8_WINNERS), (p, maximum, winners)
        assert counts[3 * 8 + 2] == expected
    print("n=8 (G310/G328/G330) reproduced at p=41,257: t=3 max 40 at "
          "((2,3),(3,2),(6,7),(7,6))", flush=True)

    prize = prize_prime(PRIZE_K)
    print(f"prize-scale Proth prime p = {prize} (k={PRIZE_K}, witness 5)", flush=True)

    phi_rows = shape_phi(8, prize)
    counts = census(8, prize)
    maximum, winners = summarize(counts, 8)
    assert maximum == 40 and counts[3 * 8 + 2] == 40, (maximum, counts[3 * 8 + 2])
    print("n=8 at prize scale: t=3 max 40, (3,2) 40", flush=True)

    ladder = []
    for n, expected_max, expected_stack, expected_winners, expected_checks in (
            (16, N16_PRIZE_MAX, 464, None, None),
            (32, N32_PRIZE_MAX, N32_PRIZE_STACK, N32_PRIZE_WINNER_COUNT, None),
            (64, N64_PRIZE_MAX, N64_PRIZE_STACK, N64_PRIZE_WINNER_COUNT,
             (N64_PRIZE_SUM, N64_PRIZE_WEIGHTED)),
            (128, N128_MAX, N128_STACK, N128_WINNER_COUNT,
             (N128_SUM, N128_WEIGHTED))):
        stage = time.time()
        phi_rows = shape_phi(n, prize)
        counts = census(n, prize)
        maximum, winners = summarize(counts, n)
        assert maximum == expected_max, (n, maximum, expected_max)
        assert counts[3 * n + 2] == expected_stack, (n, counts[3 * n + 2])
        if expected_winners is not None:
            assert len(winners) == expected_winners, (n, len(winners))
        if expected_checks is not None:
            assert checksums(counts, n) == expected_checks, (n, checksums(counts, n))
        if n == 128:
            assert sum(a * 128 + b for a, b in winners) == N128_WINNER_WEIGHTED
            assert tuple(winners[:10]) == N128_FIRST_WINNERS, winners[:10]
        ladder.append((n, maximum, len(winners), counts[3 * n + 2], time.time() - stage))
        print(f"n={n}: t=3 max {maximum} at {len(winners)} pencils, (3,2) "
              f"{counts[3 * n + 2]}, checksums {checksums(counts, n)} "
              f"[{time.time()-stage:.1f}s]", flush=True)

    stage = time.time()
    phi_rows = shape_phi(256, prize)
    counts = census(256, prize)
    maximum, winners = summarize(counts, 256)
    digest = sum(a * 256 + b for a, b in winners)
    total, weighted = checksums(counts, 256)
    assert maximum == N256_MAX, (maximum, N256_MAX)
    assert len(winners) == N256_WINNER_COUNT, len(winners)
    assert digest == N256_WINNER_WEIGHTED, (digest, N256_WINNER_WEIGHTED)
    assert counts[3 * 256 + 2] == N256_STACK
    assert (total, weighted) == (N256_SUM, N256_WEIGHTED), (total, weighted)
    assert tuple(winners[:16]) == N256_FIRST_WINNERS, winners[:16]
    for a, b in N256_CHAR_PENCILS:
        assert counts[a * 256 + b] == N256_CHAR_COUNT, ((a, b), counts[a * 256 + b])
    print(f"n=256: t=3 max {maximum} at {len(winners)} pencils, (3,2) {counts[3*256+2]}, "
          f"checksums {total}/{weighted}, winner digest {digest} "
          f"[{time.time()-stage:.1f}s]", flush=True)
    print(f"n=256 character pencils {N256_CHAR_PENCILS}: {N256_CHAR_COUNT} each", flush=True)
    print(f"n=256 first maximizers {winners[:16]}", flush=True)

    # Same listed pencils at the two further prize-scale Proth primes; no full
    # census is claimed there.
    for k, witness in EXTRA_PRIZE:
        other = prize_prime(k)
        phi_other = shape_phi(256, other)
        inverse_other = [batch_inverse(row, other) for row in phi_other]
        for a, b in N256_MULTI_PRIZE_SPOT:
            m = 256 // gcd((b - a) % 256, 256)
            expected = N256_STACK if (a, b) == (3, 2) else (
                N256_CHAR_COUNT if (a, b) in N256_CHAR_PENCILS else N256_MAX)
            assert m >= 1
            assert plain_count(256, other, phi_other, inverse_other, a, b) == expected, (k, a, b)
        print(f"p = {k}*2^128+1 (witness {witness}): listed pencils keep "
              f"{(3, 2)}={N256_STACK}, char={N256_CHAR_COUNT}, winners={N256_MAX}", flush=True)

    print(f"PASS: n=256 t=3 ceiling maximum {N256_MAX} at {N256_WINNER_COUNT} pencils "
          f"(full {256*256}-pencil census at 21*2^128+1)", flush=True)
    print(f"elapsed {time.time()-start:.1f}s", flush=True)


if __name__ == "__main__":
    main()
