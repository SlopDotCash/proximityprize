#!/usr/bin/env python3
"""Independent routes for the n=128 (x^3, x^2) t=3 ceiling bad-scalar p-scaling profile.

The primary probe ``probe_n128_t3_ceiling_p_scaling.py`` computes the count with a
coset-keyed closed form (normalised shapes + ``gamma^128 mod p`` keys).  This file
recomputes the same integers by three routes that share no code path with it.

ROUTE A (complete, raw enumeration).  For every prime ``p = 1 (mod 128)`` in
``[257, 7000000]``, enumerate ALL ``C(128, 3) = 341376`` distinct triples of ``mu_128`` and
take the size of the sum set ``|{r1 + r2 + r3}|``.  No normalised shapes, no dilations, no
cosets, no exponent keying, no linear algebra.  Because that sum set is invariant under
multiplication by ``mu_128``, its size IS the bad-scalar count, so the digest of this
route's vector must equal the keyed route's digest byte for byte; it is asserted against
the digest pinned below (printed by the primary engine in the same round).

ROUTE B (declared cells, keying-free coset union).  Build the bad set element by element
as the union of the explicit orbits ``{ratio * e : e in mu_128}`` over the shapes, with no
``pow(ratio, n, p)`` anywhere, and read ``|union|``.  Covers every counting-forced cell,
every cell where ROUTE A says 0 is bad, and the head and tail of the sweep.

ROUTE C (the merged literal MCA definition).  Recompute the count from the definition that
is MERGED on main in ``probe_n16_below_ceiling_max.py``: 2x2 elimination candidates, line
buckets over the domain, and the joint-affineness exclusion.  Run on ALL 556 merged n=8 and
ALL 279 merged n=16 anchor cells, on the spot cells at ``n = 32`` and ``n = 64``, and on
every n=128 cell with ``p <= 2000`` (the rung's cost is ``count * C(128, 2)`` line
buckets, so larger cells at n=128 are not run; stated, not hidden).  This ties the
closed-form statistic used by the sweep to the repo's own definition and shows that on the
cells it reaches the joint-affineness exclusion never fires, which is why ROUTE A and the
keyed route agree at all.

Scope.  Same finite-field scope as the primary probe: ``t = 3``, the stack (x^3, x^2), the
smooth domain mu_128 in prime fields p = 1 (mod 128) up to 7000000, plus the merged n=8 and
n=16 anchor tables.  Nothing here is a theorem in n or p; nothing about t >= 4, other
pencils, global maxima, the production regime, delta*, or the prize.
"""

import hashlib
from itertools import combinations
from math import comb, isqrt

N = 128
LIMIT = 7_000_000
ANCHOR_LIMIT = 20_000
CEILING_128 = 333440
FORCED_BOUND = 333440
# ROUTE A's stated workload per cell: |mu_128| = 128, so "all distinct triples" is C(128, 3).
# Checked before the sweep so the number quoted in the docstring is not prose-only.
TRIPLES_PER_CELL = comb(N, 3)
assert TRIPLES_PER_CELL == 341376, TRIPLES_PER_CELL

# Printed by probe_n128_t3_ceiling_p_scaling.py in this round; ROUTE A recomputes the
# vector independently and asserts equality with it.
PRIMARY_VECTOR_DIGEST = "8ee8c189b1fb233669291eb8c572a31c9e7a68dc54faf4bb6fa8d068281496d4"

# Merged in-tree probe_n16_below_ceiling_max.py (PR #267) and G330 published integers.
CEILING_EXCEPTIONS_16 = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
N16_COUNT = 279
N16_GENERIC = 464
N8_COUNT = 556
N8_GENERIC = 40
SPOT_32_65537 = 3264
SPOT_64_65537 = 13761
SPOT_64_6700417 = 34176
SPOT_128_257 = 257
SPOT_128_65537 = 61313
ROUTE_C_128_BOUND = 2000


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


def order_element(p, n):
    for candidate in range(2, p):
        element = pow(candidate, (p - 1) // n, p)
        if pow(element, n // 2, p) == p - 1:
            assert pow(element, n, p) == 1
            return element
    raise AssertionError("no element of order %d modulo %d" % (n, p))


def subgroup(p, n):
    generator = order_element(p, n)
    values = [1]
    for _ in range(n - 1):
        values.append(values[-1] * generator % p)
    assert len(set(values)) == n and values[-1] * generator % p == 1
    return values


def raw_census(p, n):
    """ROUTE A: distinct sums over all distinct triples of mu_n; size read directly."""
    elements = subgroup(p, n)
    sums = set()
    add = sums.add
    for a, b, c in combinations(elements, 3):
        add((a + b + c) % p)
    return len(sums), (1 if 0 in sums else 0)


def union_census(p, n):
    """ROUTE B: explicit element-by-element union of the cosets, no exponent keying."""
    elements = subgroup(p, n)
    ys = elements[1:]
    union = set()
    add = union.add
    for y, z in combinations(ys, 2):
        ratio = (1 + y + z) % p
        if ratio == 0:
            add(0)
            continue
        for element in elements:
            add(ratio * element % p)
    return len(union), (1 if 0 in union else 0)


def affine_on(values, points, xs, p):
    if len(points) <= 2:
        return True
    first, second = points[0], points[1]
    slope = (values[second] - values[first]) * pow((xs[second] - xs[first]) % p, -1, p) % p
    intercept = (values[first] - slope * xs[first]) % p
    return all((intercept + slope * xs[index] - values[index]) % p == 0 for index in points)


def literal_census(n, p, threshold=3):
    """ROUTE C: the merged in-tree definition, verbatim semantics, no closed form."""
    xs = subgroup(p, n)
    powers = [[pow(x, e, p) for x in xs] for e in range(n)]
    pair_inv = {(i, j): pow((xs[j] - xs[i]) % p, -1, p)
                for i, j in combinations(range(n), 2)}
    u0, u1 = powers[3], powers[2]
    candidates = set()
    for i, j, k in combinations(range(n), 3):
        a11 = (u1[j] - u1[i]) % p
        a12 = (xs[i] - xs[j]) % p
        a21 = (u1[k] - u1[i]) % p
        a22 = (xs[i] - xs[k]) % p
        det = (a11 * a22 - a12 * a21) % p
        if det:
            b1 = (u0[j] - u0[i]) % p
            b2 = (u0[k] - u0[i]) % p
            candidates.add((((-b1) * a22 - (a12 * (-b2))) % p) * pow(det, -1, p) % p)
    min_pairs = threshold * (threshold - 1) // 2
    bad = set()
    for gamma in candidates:
        values = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
        lines = {}
        for i, j in combinations(range(n), 2):
            slope = (values[j] - values[i]) * pair_inv[(i, j)] % p
            intercept = (values[i] - slope * xs[i]) % p
            lines.setdefault((slope, intercept), []).append((i, j))
        for _line, pairs in lines.items():
            if len(pairs) < min_pairs:
                continue
            witness = [index for index in range(n)
                       if values[index] == (_line[1] + _line[0] * xs[index]) % p]
            if len(witness) < threshold:
                continue
            if not (affine_on(u0, witness, xs, p) and affine_on(u1, witness, xs, p)):
                bad.add(gamma)
                break
    return len(bad), (1 if 0 in bad else 0)


def main():
    flags = sieve(LIMIT)

    # 1. Merged anchors by BOTH ROUTE A and ROUTE C, cell by cell.
    primes8 = primes_one_mod(8, ANCHOR_LIMIT, flags)
    raw8 = [(p,) + raw_census(p, 8) for p in primes8]
    lit8 = [(p,) + literal_census(8, p) for p in primes8]
    exc8_raw = [(p, c) for p, c, _ in raw8 if c != N8_GENERIC]
    exc8_lit = [(p, c) for p, c, _ in lit8 if c != N8_GENERIC]
    assert len(primes8) == N8_COUNT, len(primes8)
    assert exc8_raw == [(17, 16)] and exc8_lit == [(17, 16)], (exc8_raw, exc8_lit)
    assert raw8 == lit8
    print("merged anchor n=8 on all %d cells: ROUTE A and ROUTE C agree entry by entry "
          "(count 40 at %d cells, single exception 17:16)"
          % (len(primes8), len(primes8) - 1))

    primes16 = primes_one_mod(16, ANCHOR_LIMIT, flags)
    raw16 = [(p,) + raw_census(p, 16) for p in primes16]
    lit16 = [(p,) + literal_census(16, p) for p in primes16]
    exc16_raw = dict((p, c) for p, c, _ in raw16 if c != N16_GENERIC)
    exc16_lit = dict((p, c) for p, c, _ in lit16 if c != N16_GENERIC)
    assert len(primes16) == N16_COUNT, len(primes16)
    assert exc16_raw == CEILING_EXCEPTIONS_16, sorted(exc16_raw.items())
    assert exc16_lit == CEILING_EXCEPTIONS_16, sorted(exc16_lit.items())
    assert raw16 == lit16
    print("merged anchor n=16 on all %d cells: ROUTE A and ROUTE C agree entry by entry "
          "and both reproduce the published 464 outside the 34-prime exception table %s"
          % (len(primes16), sorted(exc16_lit)))

    # 2. ROUTE A over the COMPLETE n=128 sweep.
    primes = primes_one_mod(N, LIMIT, flags)
    rows = []
    for p in primes:
        count, zero = raw_census(p, N)
        assert count % N == zero, (p, count, zero)
        assert count <= p, (p, count)
        rows.append((p, count, (count - zero) // N, zero))
    total = len(rows)
    raw_by_p = dict((p, (c, k, z)) for p, c, k, z in rows)
    counts = [r[1] for r in rows]
    at_ceiling = [r for r in rows if r[1] == CEILING_128]
    below = [r for r in rows if r[1] != CEILING_128]
    digest = hashlib.sha256()
    for row in rows:
        digest.update(("%d,%d,%d,%d;" % row).encode("ascii"))
    assert digest.hexdigest() == PRIMARY_VECTOR_DIGEST, digest.hexdigest()
    assert max(counts) == CEILING_128, max(counts)
    assert raw_by_p[257][0] == SPOT_128_257 and raw_by_p[65537][0] == SPOT_128_65537
    print("ROUTE A raw distinct-triple enumeration: %d cells, ceiling %d at %d, %d below; "
          "first ceiling cell p=%s, largest below-ceiling cell p=%s; digest asserted equal "
          "to the primary keyed engine"
          % (total, CEILING_128, len(at_ceiling), len(below),
             at_ceiling[0][0] if at_ceiling else None,
             below[-1][0] if below else None))
    zero_rows = [r for r in rows if r[3] == 1]
    print("ROUTE A 0-bad cells: %d, smallest %d, largest %d, list %s"
          % (len(zero_rows), zero_rows[0][0], zero_rows[-1][0],
             [p for p, _, _, _ in zero_rows]))
    forced = [r for r in rows if r[0] <= FORCED_BOUND]
    forced_full = [r for r in forced if r[1] in (r[0] - 1, r[0])]
    genuine = [r for r in rows if r[0] > FORCED_BOUND]
    genuine_below = [r for r in genuine if r[1] != CEILING_128]
    print("ROUTE A forced cells (p <= %d): %d, complete saturation %d, cosets left unhit "
          "%d; genuine regime: %d primes, %d below ceiling, %d at it"
          % (FORCED_BOUND, len(forced), len(forced_full), len(forced) - len(forced_full),
             len(genuine), len(genuine_below), len(genuine) - len(genuine_below)))
    print("ROUTE A aggregate checksums: sum count = %d, sum p*count = %d, distinct counts "
          "= %d, vector digest sha256 %s"
          % (sum(counts), sum(p * c for p, c, _, _ in rows), len(set(counts)),
             digest.hexdigest()))

    # 3. ROUTE B on a declared cell set: every forced cell, every 0-bad cell, the head and
    #    the tail of the sweep.
    b_cells = sorted(set([p for p, _, _, _ in rows if p <= FORCED_BOUND]
                         + [p for p, _, _, _ in zero_rows]
                         + [p for p, _, _, _ in rows[:12]]
                         + [p for p, _, _, _ in rows[-12:]]))
    disagreements = 0
    for p in b_cells:
        count, zero = union_census(p, N)
        if (count, zero) != (raw_by_p[p][0], raw_by_p[p][2]):
            disagreements += 1
            print("ROUTE B DISAGREEMENT at p=%d: (%d,%d) vs (%d,%d)"
                  % (p, count, zero, raw_by_p[p][0], raw_by_p[p][2]))
    assert disagreements == 0
    print("ROUTE B keying-free explicit coset union on %d cells (all %d cells with "
          "p <= %d, the %d 0-bad cells, the 12 head and 12 tail cells): 0 disagreements "
          "with ROUTE A"
          % (len(b_cells), len([p for p in b_cells if p <= FORCED_BOUND]), FORCED_BOUND,
             len(zero_rows)))

    # 4. ROUTE C on the reachable n=128 cells and on the other-rung spot cells.
    spot_c = []
    for n, p, expected in ((32, 65537, SPOT_32_65537), (64, 65537, SPOT_64_65537),
                           (64, 6700417, SPOT_64_6700417)):
        got, _ = literal_census(n, p)
        assert got == expected, (n, p, got, expected)
        spot_c.append((n, p, got))
    c128 = [p for p, _, _, _ in rows if p <= ROUTE_C_128_BOUND]
    lit128 = [(p,) + literal_census(N, p) for p in c128]
    for p, count, zero in lit128:
        assert (count, zero) == (raw_by_p[p][0], raw_by_p[p][2]), p
        assert count % N == zero
    print("ROUTE C literal MCA definition (2x2 elimination + line buckets + joint-affineness "
          "exclusion): spot cells %s and every n=128 cell with p <= %d -> %s, all agreeing "
          "with ROUTE A"
          % (spot_c, ROUTE_C_128_BOUND, [(p, c) for p, c, _ in lit128]))
    print("PASS: three independent routes agree with the keyed primary engine on the "
          "complete %d-cell n=128 sweep (ROUTE A digest pinned to the primary), on %d "
          "ROUTE B cells, and on the merged n=8 (%d cells) and n=16 (%d cells) tables plus "
          "the ROUTE C cells listed"
          % (total, len(b_cells), len(primes8), len(primes16)))


if __name__ == "__main__":
    main()
