#!/usr/bin/env python3
"""Exact n=256 ceiling (t=3) monomial-pencil census at three prize-scale primes.

Object.  Fix a prime ``p = 1 (mod n)``, a generator ``g`` of order ``n = 256`` in
``F_p``, the smooth domain ``x_i = g^i``, and the dimension-two code of affine
words ``c0 + c1*x``.  For the monomial pencil ``(u0, u1) = (x^a, x^b)`` the
*ceiling* bad scalars are the gammas for which ``u0 + gamma*u1`` agrees with an
affine word on some triple while ``(u0, u1)`` is not jointly affine on that
triple (the ``pairJointAgreesOn`` exclusion of the repository MCA event).  This
probe runs the full ``n^2 = 65536``-pencil census of that count at

    p = 21*2^128 + 1,   p = 111*2^128 + 1,   p = 123*2^128 + 1

and asserts that the complete count vector is identical at the three primes: all
65536 integers are compared exactly (a SHA-256 of the vector is printed for each
prime), the maximum, maximizer count and digest, both checksums, the ``(3,2)``
count and the four quadratic-character counts are pinned, and eight fixed
pencils are recounted at each prime from the definition (all ``C(256,3)``
triples, direct 3x3 determinants, no coset reasoning).

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

Pinned integers (k = 21, first established by
``probe_n256_t3_ceiling_max.py``):  maximum ``2746624 = C(256,3) - 256*66`` at
exactly 3584 pencils, ``(3,2)`` count 2731264, quadratic-character count
532481, checksums 115947536562 / 3829109404545625, maximizer digest
(sum of ``a*256+b``) 118359808.  The new claim of this probe is that the same
complete cell holds at the two further prize-scale Proth primes.

Scope (read before citing).  Finite fields only; smooth domain ``mu_256``;
dimension-two affine code; monomial pencils only -- this is **not** a maximum
over arbitrary word pairs or stacks, and it is not a field-uniform theorem in
``p``.  ``n = 256`` is far below the production ``n = 2^30/2^32``; nothing here
is a production-regime statement, a ``delta*`` claim, or a step toward the
prize.  Stdlib only, deterministic, integer arithmetic only.
"""

import hashlib
import time
from math import gcd

PRIZE_EXP = 128
PRIZE_KS = ((21, 5), (111, 5), (123, 7))
N = 256

# Published anchors reproduced by this code path.
N8_CELLS = {41: 40, 257: 40}
N8_WINNERS = ((2, 3), (3, 2), (6, 7), (7, 6))
N16_PRIZE_MAX = 464

# Pinned n=256 cell (established at k=21 by probe_n256_t3_ceiling_max.py).
N256_MAX = 2746624
N256_WINNER_COUNT = 3584
N256_STACK = 2731264
N256_SUM = 115947536562
N256_WEIGHTED = 3829109404545625
N256_WINNER_WEIGHTED = 118359808
N256_CHAR_PENCILS = ((128, 127), (128, 255), (129, 2), (129, 130))
N256_CHAR_COUNT = 532481
LITERAL_PENCILS = ((2, 11), (3, 2), (128, 127), (129, 2),
                   (7, 135), (100, 200), (255, 1), (16, 17))


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
    assert not any(phi[0]) and not any(phi[1])
    assert all(value == 1 for value in phi[2])
    return xs, phi


def square_table(table, p):
    return [[value * value % p for value in row] for row in table]


def census(n, p, phi_rows):
    """Exact t=3 ceiling counts for all n^2 ordered pencils (coset-key engine)."""
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


def literal_count(n, p, xs, powers, a, b):
    """Definition-level count over all C(n,3) triples (direct determinants)."""
    row_a = powers[a]
    row_b = powers[b]
    denom = []
    for i in range(n - 2):
        xi = xs[i]
        for j in range(i + 1, n - 1):
            xj = xs[j]
            for k in range(j + 1, n):
                xk = xs[k]
                denom.append(((xj - xi) * row_b[k] + (xi - xk) * row_b[j]
                              + (xk - xj) * row_b[i]) % p)
    prefix = [1] * (len(denom) + 1)
    for index, value in enumerate(denom):
        prefix[index + 1] = prefix[index] * (value if value else 1) % p
    inverse = pow(prefix[-1], -1, p)
    inverses = [0] * len(denom)
    for index in range(len(denom) - 1, -1, -1):
        value = denom[index]
        if value:
            inverses[index] = inverse * prefix[index] % p
            inverse = inverse * value % p
    seen = set()
    add = seen.add
    position = 0
    for i in range(n - 2):
        xi = xs[i]
        for j in range(i + 1, n - 1):
            xj = xs[j]
            for k in range(j + 1, n):
                xk = xs[k]
                db = denom[position]
                if db:
                    da = ((xj - xi) * row_a[k] + (xi - xk) * row_a[j]
                          + (xk - xj) * row_a[i]) % p
                    add((-da * inverses[position]) % p)
                position += 1
    return len(seen)


def prize_prime(k, witness):
    p = k * (2 ** PRIZE_EXP) + 1
    assert k < 2 ** PRIZE_EXP
    assert pow(witness, (p - 1) // 2, p) == p - 1, k
    return p


def cell(p):
    start = time.time()
    xs, phi_rows = shape_phi(N, p)
    counts = census(N, p, phi_rows)
    maximum, winners = summarize(counts, N)
    digest = sum(a * N + b for a, b in winners)
    total, weighted = checksums(counts, N)
    char = tuple(counts[a * N + b] for a, b in N256_CHAR_PENCILS)
    stack = counts[3 * N + 2]
    vector = hashlib.sha256(
        ",".join(str(counts[code]) for code in range(N * N)).encode()).hexdigest()
    print(f"p = {p}: t=3 max {maximum} at {len(winners)} pencils, (3,2) {stack}, "
          f"checksums {total}/{weighted}, winner digest {digest}, "
          f"char {char}, vector sha256 {vector} [{time.time()-start:.1f}s]", flush=True)
    return counts, xs, (maximum, len(winners), stack, char, total, weighted, digest)


def main():
    start = time.time()

    for p, expected in N8_CELLS.items():
        _, phi = shape_phi(8, p)
        counts = census(8, p, phi)
        maximum, winners = summarize(counts, 8)
        assert (maximum, tuple(winners)) == (expected, N8_WINNERS), (p, maximum, winners)
    print("n=8 (G310/G328/G330) reproduced at p=41,257: t=3 max 40", flush=True)

    first_k, first_witness = PRIZE_KS[0]
    first_p = prize_prime(first_k, first_witness)
    _, phi16 = shape_phi(16, first_p)
    counts16 = census(16, first_p, phi16)
    assert max(counts16.values()) == N16_PRIZE_MAX
    print(f"n=16 at p = {first_k}*2^128+1: t=3 max {N16_PRIZE_MAX} reproduced", flush=True)

    cells = {}
    full_counts = {}
    literal_rows = {}
    for k, witness in PRIZE_KS:
        p = prize_prime(k, witness)
        counts, xs, summary = cell(p)
        cells[k] = summary
        full_counts[k] = counts

        powers = [[1] * N for _ in range(N)]
        for exponent in range(1, N):
            previous = powers[exponent - 1]
            current = powers[exponent]
            for index in range(N):
                current[index] = previous[index] * xs[index] % p
        stage = time.time()
        literal_rows[k] = tuple(literal_count(N, p, xs, powers, a, b)
                                for a, b in LITERAL_PENCILS)
        for (a, b), value in zip(LITERAL_PENCILS, literal_rows[k]):
            assert value == counts[a * N + b], (k, a, b, value, counts[a * N + b])
        print(f"p = {p}: literal C(256,3) enumeration matches the census on "
              f"{len(LITERAL_PENCILS)} pencils, values {literal_rows[k]} "
              f"[{time.time()-stage:.1f}s]", flush=True)

    reference = cells[first_k]
    assert reference == (N256_MAX, N256_WINNER_COUNT, N256_STACK,
                         (N256_CHAR_COUNT,) * 4, N256_SUM, N256_WEIGHTED,
                         N256_WINNER_WEIGHTED), reference
    for k, _ in PRIZE_KS[1:]:
        assert cells[k] == reference, (k, cells[k], reference)
        assert full_counts[k] == full_counts[first_k], (k, "count vector differs")
    print(f"PASS: the full {N*N}-entry n=256 t=3 count vector is identical at k = "
          f"{', '.join(str(k) for k, _ in PRIZE_KS)}: max {N256_MAX} at "
          f"{N256_WINNER_COUNT} pencils, (3,2) {N256_STACK}, char {N256_CHAR_COUNT}, "
          f"checksums {N256_SUM}/{N256_WEIGHTED}, digest {N256_WINNER_WEIGHTED}", flush=True)
    print(f"elapsed {time.time()-start:.1f}s", flush=True)


if __name__ == "__main__":
    main()
