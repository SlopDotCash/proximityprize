#!/usr/bin/env python3
"""Independent crosscheck for the n=256 t=3 ceiling-maximum census.

This file recomputes the n=256 integers of
``probe_n256_t3_ceiling_max.py`` through three independent routes and hard-asserts
that all of them agree:

1. **Plain coset engine.**  The per-pencil count is ``m * (#nonzero cosets) +
   [0 is bad]`` with the coset key ``(-phi_a/phi_b)^m`` computed by a plain
   per-shape modular power.  The main probe instead tabulates ``phi^m`` and
   uses the identity ``(-phi_a/phi_b)^m = phi_a^m/phi_b^m`` (m even), so the two
   code paths share only the published characterisation, not the evaluation.

2. **Swap law.**  Reversing the pencil maps every nonzero bad scalar ``gamma``
   to ``1/gamma``: ``u1 + gamma*u0`` is affine on a triple iff
   ``u0 + gamma^{-1}*u1`` is, and the joint-affineness exclusion is symmetric.
   Hence, with ``z_ab = [0 is bad for (a,b)]``,
   ``count(b,a) = count(a,b) - z_ab + z_ba``, and ``z`` is decided by the zero
   patterns of the two exponent rows (a bitmask test).  This halves the exact
   enumeration; the law itself is asserted exhaustively at n = 64 over all
   ordered pairs and on a deterministic n = 256 sample.

3. **Literal triple enumeration.**  For a fixed list of pencils at n = 256 all
   ``C(256,3)`` triples are enumerated, the 3x3 collinearity determinants
   ``D_a``, ``D_b`` are evaluated from the point values directly (no
   Vandermonde factorisation, no complete-homogeneous closed form, no coset
   reasoning) and every nonzero ratio ``-D_a/D_b`` is inserted into a set; the
   set size is the count.  This is the definition-level check of the integers.

Published anchors reproduced by the plain engine: n=8 (40 at p=41,257), n=16
(464), n=32 (4640, 56 maximizers, (3,2)=4512), n=64 (40512, 224 maximizers,
(3,2)=39744) at the prize-scale prime.

Scope.  Finite fields only; smooth domain mu_256; dimension-two affine code;
monomial pencils only; the full n=256 census is at p = 21*2^128 + 1 only.  This
is not a production-regime statement, not a ``delta*`` claim, and it says
nothing about arbitrary word pairs or stacks.  Stdlib only, deterministic,
integer arithmetic only.
"""

import time
from math import gcd

PRIZE_EXP = 128
N = 256
PRIZE = 21 * 2 ** PRIZE_EXP + 1

N8_CELLS = ((41, 40), (257, 40))
N8_WINNERS = ((2, 3), (3, 2), (6, 7), (7, 6))
N16_PRIZE_MAX = 464
N32_PRIZE_MAX = 4640
N32_PRIZE_WINNER_COUNT = 56
N32_PRIZE_STACK = 4512
N64_PRIZE_MAX = 40512
N64_PRIZE_WINNER_COUNT = 224
N64_PRIZE_STACK = 39744
N64_PRIZE_SUM = 96271090
N64_PRIZE_WEIGHTED = 203372423673

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
        raise AssertionError(f"{n} does not divide p-1")
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError("no element of order n")


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


def plain_count(n, p, phi, inverse_phi, a, b):
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


def zero_bitmasks(phi, slots):
    masks = []
    for row in phi:
        bits = 0
        for slot in range(slots):
            if row[slot] == 0:
                bits |= 1 << slot
        masks.append(bits)
    return masks


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


def plain_census(n, p, phi):
    inverse_phi = [batch_inverse(row, p) for row in phi]
    counts = {}
    for a in range(n):
        for b in range(n):
            counts[a * n + b] = plain_count(n, p, phi, inverse_phi, a, b)
    return counts


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
                db = ((xj - xi) * row_b[k] + (xi - xk) * row_b[j]
                      + (xk - xj) * row_b[i]) % p
                denom.append(db)
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


def main():
    start = time.time()

    for p, expected in N8_CELLS:
        xs, phi = shape_phi(8, p)
        counts = plain_census(8, p, phi)
        maximum, winners = summarize(counts, 8)
        assert (maximum, tuple(winners)) == (expected, N8_WINNERS), (p, maximum, winners)
    print("n=8 (p=41,257): plain engine reproduces t=3 max 40 at "
          "((2,3),(3,2),(6,7),(7,6))", flush=True)

    phi = shape_phi(16, PRIZE)[1]
    counts = plain_census(16, PRIZE, phi)
    assert max(counts.values()) == N16_PRIZE_MAX, max(counts.values())
    phi = shape_phi(32, PRIZE)[1]
    counts = plain_census(32, PRIZE, phi)
    maximum, winners = summarize(counts, 32)
    assert maximum == N32_PRIZE_MAX and len(winners) == N32_PRIZE_WINNER_COUNT
    assert counts[3 * 32 + 2] == N32_PRIZE_STACK
    phi = shape_phi(64, PRIZE)[1]
    counts = plain_census(64, PRIZE, phi)
    maximum, winners = summarize(counts, 64)
    assert maximum == N64_PRIZE_MAX and len(winners) == N64_PRIZE_WINNER_COUNT
    assert counts[3 * 64 + 2] == N64_PRIZE_STACK
    assert checksums(counts, 64) == (N64_PRIZE_SUM, N64_PRIZE_WEIGHTED)
    print("n=16/32/64 at prize scale: plain engine reproduces 464 / 4640 (56 maximizers, "
          "(3,2)=4512) / 40512 (224 maximizers, (3,2)=39744, checksums pinned)", flush=True)

    xs, phi = shape_phi(N, PRIZE)
    inverse_phi = [batch_inverse(row, PRIZE) for row in phi]
    slots = len(phi[0])
    masks = zero_bitmasks(phi, slots)

    # Swap law: exhaustive check at n=64 over all ordered pairs.
    xs64, phi64 = shape_phi(64, PRIZE)
    inv64 = [batch_inverse(row, PRIZE) for row in phi64]
    masks64 = zero_bitmasks(phi64, len(phi64[0]))
    for a in range(64):
        for b in range(64):
            if a == b:
                continue
            z_ab = 1 if masks64[a] & ~masks64[b] else 0
            z_ba = 1 if masks64[b] & ~masks64[a] else 0
            assert plain_count(64, PRIZE, phi64, inv64, b, a) == (
                plain_count(64, PRIZE, phi64, inv64, a, b) - z_ab + z_ba), (a, b)
    print("swap law (count(b,a) = count(a,b) - z_ab + z_ba): exhaustive at n=64 over "
          "all 4032 ordered pairs", flush=True)

    sample = [(a, (a * 91 + 5) % N) for a in range(0, N, 8) if (a * 91 + 5) % N != a]
    for a, b in sample:
        if a > b:
            a, b = b, a
        z_ab = 1 if masks[a] & ~masks[b] else 0
        z_ba = 1 if masks[b] & ~masks[a] else 0
        assert plain_count(N, PRIZE, phi, inverse_phi, b, a) == (
            plain_count(N, PRIZE, phi, inverse_phi, a, b) - z_ab + z_ba), (a, b)
    print(f"swap law: n=256 sample of {len(sample)} pairs agrees in both directions", flush=True)

    # Exact plain counts for a<b, swap-derived mirrors, exact diagonal.
    stage = time.time()
    counts = {}
    for a in range(N):
        for b in range(a + 1, N):
            value = plain_count(N, PRIZE, phi, inverse_phi, a, b)
            z_ab = 1 if masks[a] & ~masks[b] else 0
            z_ba = 1 if masks[b] & ~masks[a] else 0
            counts[a * N + b] = value
            counts[b * N + a] = value - z_ab + z_ba
    for a in range(N):
        counts[a * N + a] = plain_count(N, PRIZE, phi, inverse_phi, a, a)
    print(f"n=256 plain census (a<b exact + swap mirrors + diagonal) done in "
          f"{time.time()-stage:.1f}s", flush=True)

    maximum, winners = summarize(counts, N)
    digest = sum(a * N + b for a, b in winners)
    total, weighted = checksums(counts, N)
    assert maximum == N256_MAX, maximum
    assert len(winners) == N256_WINNER_COUNT, len(winners)
    assert digest == N256_WINNER_WEIGHTED, digest
    assert counts[3 * N + 2] == N256_STACK
    assert (total, weighted) == (N256_SUM, N256_WEIGHTED), (total, weighted)
    for a, b in N256_CHAR_PENCILS:
        assert counts[a * N + b] == N256_CHAR_COUNT, (a, b)
    print(f"n=256 plain census agrees with the table engine: max {maximum} at "
          f"{len(winners)} pencils, (3,2) {counts[3*N+2]}, checksums {total}/{weighted}, "
          f"winner digest {digest}", flush=True)

    # Definition-level literal enumeration on the fixed pencil list.
    powers = [[1] * N for _ in range(N)]
    for exponent in range(1, N):
        previous = powers[exponent - 1]
        current = powers[exponent]
        for index in range(N):
            current[index] = previous[index] * xs[index] % PRIZE
    stage = time.time()
    for a, b in LITERAL_PENCILS:
        literal = literal_count(N, PRIZE, xs, powers, a, b)
        assert literal == counts[a * N + b], ((a, b), literal, counts[a * N + b])
    print(f"literal all-triples enumeration at n=256 matches the census on "
          f"{len(LITERAL_PENCILS)} pencils in {time.time()-stage:.1f}s", flush=True)

    print(f"PASS: independent crosscheck of the n=256 t=3 census "
          f"(max {N256_MAX}, {N256_WINNER_COUNT} maximizers, checksums "
          f"{N256_SUM}/{N256_WEIGHTED})", flush=True)
    print(f"elapsed {time.time()-start:.1f}s", flush=True)


if __name__ == "__main__":
    main()
