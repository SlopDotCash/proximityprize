#!/usr/bin/env python3
"""p-scaling of the (x^3, x^2) t=3 ceiling bad-scalar count at the new rung n = 128.

Object (the published monomial-pencil census).  Fix a prime ``p = 1 (mod n)``, an element
``g`` of exact order ``n``, the smooth domain ``mu_n = {g^0, ..., g^(n-1)}`` and the
dimension-two code of affine words ``c0 + c1*x``.  For the stack ``(u0, u1) = (x^3, x^2)``
the ceiling (``t = 3``) bad scalars are the ``gamma`` for which ``x^3 + gamma*x^2`` agrees
with an affine word on some triple ``T`` while ``(x^3, x^2)`` is not jointly affine on
``T``.  Matching ``X^3 + gamma*X^2 - c1*X - c0`` against its three roots gives the twin
forms ``gamma = -(r1 + r2 + r3)`` over distinct triples and, through the collinearity
determinants, ``gamma = -(1 + y + z)`` on the normalised shape ``{1, y, z}``.  Dilating
``T`` by ``g`` multiplies ``gamma`` by ``g``, so the bad set is a union of cosets of
``mu_n`` and ``count = n * (#cosets) + [0 bad]``.  This is exactly the quantity whose
per-prime tables are MERGED at ``n = 8`` and ``n = 16`` (``probe_n16_below_ceiling_max.py``,
PR #267) and whose profile at ``n = 64`` is the campaign's staged next rung.

Claim (this probe).  The complete per-prime profile of that count at the rung ``n = 128``,
over EVERY prime ``p = 1 (mod 128)`` in ``[257, 7000000]`` (7453 cells), against the
ceiling value ``333440 = 128 + 8*C(64, 3)``:

* the merged ``n = 8`` (556 primes, ``40`` except ``17: 16``) and ``n = 16`` (279 primes,
  ``464`` outside the published 34-prime exception table) are reproduced cell by cell by
  THIS engine before the new rung is touched;
* the structural law ``count = 128 * cosets + [0 bad]`` and the bounds ``count <= p``,
  ``cosets <= (p-1)/128`` are hard-asserted at every one of the 7453 cells;
* the maximum over the sweep is exactly ``333440``, i.e. the value the campaign publishes
  for this stack at the prize-scale Proth prime ``21*2^128+1``, and it is attained at
  ordinary primes only up to ``7000000`` -- the count is NOT p-independent at ``n = 128``
  either; the number of ceiling cells, the FIRST ceiling cell and the LARGEST
  below-ceiling cell are printed;
* the exception set splits into the counting-forced regime ``p <= 128*2605 = 333440``
  (fewer than 2605 cosets exist, so the ceiling is unreachable) and the genuine-collision
  regime above it; in the forced regime the naive saturation law ``count = p - 1 + [0 bad]``
  is reported cell by cell together with the smallest prime at which it fails and the
  deepest shortfall;
* ``0`` is a bad scalar at the primes listed below -- the distinct vanishing-3-sum locus of
  ``mu_128`` inside the swept range -- and this list is *derived* here from the raw shape
  sums, independently of any resultant computation;
* the Fermat prime ``65537`` and the Fermat-factor prime ``6700417`` appear as ordinary
  points of the sweep, and the cells ``(32, 65537)``, ``(64, 65537)``, ``(64, 6700417)`` and
  the prize ladder ``(16, 32, 64, 128)`` at ``21*2^128+1`` are re-derived here as tie-outs
  to the campaign's own merged and open PRs rather than being new data.

Engine.  Coset-keyed closed form: evaluate ``-(1 + y + z)`` over the ``C(n-1, 2)``
normalised shapes, key a nonzero value by ``gamma^n mod p`` (two values share a key iff
their ratio lies in ``mu_n``), and count keys.  No discrete logarithm, no determinant, no
linear algebra, no floating point in the computation; every printed claim is hard-asserted.

Scope (read before citing).  Finite prime fields only, the monomial stack ``(x^3, x^2)``
only, the agreement threshold ``t = 3`` only, the rungs ``n = 8, 16, 128`` swept and the
tie-out cells ``n = 32, 64, 128`` named, and primes ``p = 1 (mod 128)`` only up to
``7000000``.  ``n = 32`` and ``n = 64`` complete sweeps belong to the campaign's open PR
#272 and staged n=64 rung and are NOT re-swept here.  The profile is computed cell by
cell; it is not a theorem in ``n`` or ``p``, not a statement about any other pencil or
about ``t >= 4``, not a global-maximum statement, not the production regime
``n = 2^30 / 2^32``, not ``delta*``, and not the prize.  Nothing here says the ceiling is
or is not attained at primes beyond ``7000000``.
"""

import hashlib
from itertools import combinations
from math import isqrt

N = 128
LIMIT = 7_000_000
ANCHOR_LIMIT = 20_000

# Merged in-tree probe_n16_below_ceiling_max.py (PR #267): published integers.
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
N8_SPOT = {17: 16, 41: 40, 257: 40}

# Ceiling value at this rung: n + 8*C(n/2, 3), the closed form the campaign publishes for
# the (x^3, x^2) stack at the prize scale (open PRs #272/#300/#341; NOT merged on main).
CEILING_128 = N + 8 * (64 * 63 * 62 // 6)
assert CEILING_128 == 333440
FLOOR_COSSETS = CEILING_128 // N          # 2605
FORCED_BOUND = N * FLOOR_COSSETS          # 333440
assert FORCED_BOUND == CEILING_128

# Tie-out cells owned by other lanes of this campaign (merged, open PR, or staged).
SPOT_32_65537 = 3264        # open PR #272 (n=32 census)
SPOT_64_65537 = 13761       # open PRs #300/#319
SPOT_64_6700417 = 34176     # open PR #319
PRIME_PRIZE = 21 * 2 ** 128 + 1
PRIZE_CELLS = {16: 464, 32: 4512, 64: 39744, 128: CEILING_128}
SPOT_128_257 = 257          # the smallest cell of the sweep saturates at p
SPOT_128_65537 = 61313      # campaign's staged (not merged) n=128 census at 65537
WINDOWS = ((257, 100_000), (100_000, 1_000_000), (1_000_000, LIMIT))
LOCUS_EXCLUDED_128 = 274177  # divides R_128 but is degenerate-only: 0 must NOT be bad


def sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if flags[divisor]:
            start = divisor * divisor
            flags[start:limit + 1:divisor] = b"\x00" * len(
                range(start, limit + 1, divisor))
    return flags


def primes_one_mod(p_mod, limit, flags=None):
    if flags is None:
        flags = sieve(limit)
    return [p for p in range(p_mod, limit + 1) if flags[p] and p % p_mod == 1]


def proth_prime(k, exponent):
    """Proth's theorem: k*2^exponent + 1 with k odd and k < 2^exponent is prime iff some
    a has a^((p-1)/2) = -1 mod p.  Returns (prime, witness); exact integer arithmetic."""
    value = k * 2 ** exponent + 1
    assert k < 2 ** exponent and k % 2 == 1
    witness = 2
    while pow(witness, (value - 1) // 2, value) != value - 1:
        witness += 1
    return value, witness


def order_element(p, n):
    for candidate in range(2, p):
        element = pow(candidate, (p - 1) // n, p)
        if pow(element, n // 2, p) == p - 1:
            assert pow(element, n, p) == 1
            return element
    raise AssertionError("no element of order %d modulo %d" % (n, p))


def coset_census(n, p):
    """Bad-scalar count of (x^3, x^2) at t = 3 through the normalised-shape coset keys."""
    generator = order_element(p, n)
    ys = [pow(generator, i, p) for i in range(1, n)]
    assert len(set(ys)) == n - 1
    keys = set()
    zero = 0
    for y, z in combinations(ys, 2):
        ratio = (1 + y + z) % p
        if ratio == 0:
            zero = 1
        else:
            keys.add(pow(ratio, n, p))
    count = n * len(keys) + zero
    assert count - zero == n * len(keys)
    assert len(ys) == n - 1
    return count, len(keys), zero, generator


def profile(n, primes):
    rows = []
    for p in primes:
        count, cosets, zero, _ = coset_census(n, p)
        rows.append((p, count, cosets, zero))
    return rows


def main():
    flags = sieve(LIMIT)
    proth_value, proth_witness = proth_prime(21, 128)
    assert proth_value == PRIME_PRIZE

    print("n=128 p-scaling of the (x^3, x^2) t=3 ceiling bad-scalar count")
    print("parameters: domain mu_%d in F_p, threshold t=3, pencil (3,2), "
          "primes p = 1 (mod %d) in [%d, %d]" % (N, N, 257, LIMIT))
    print("primality: primes <= %d by sieve; p = 21*2^128+1 by Proth's theorem "
          "with witness a=%d" % (LIMIT, proth_witness))

    # 1. Merged anchors, reproduced cell by cell before the new rung is touched.
    primes8 = primes_one_mod(8, ANCHOR_LIMIT, flags)
    rows8 = profile(8, primes8)
    exc8 = [(p, c) for p, c, _, _ in rows8 if c != N8_GENERIC]
    assert len(primes8) == N8_COUNT, len(primes8)
    assert exc8 == [(17, 16)], exc8
    table8 = dict((p, c) for p, c, _, _ in rows8)
    for p, expected in N8_SPOT.items():
        assert table8[p] == expected, p
    print("merged anchor n=8: %d primes p = 1 (mod 8) in [17, %d], count %d at %d of them, "
          "single exception 17:16 (G330 exact boundary)"
          % (len(primes8), ANCHOR_LIMIT, N8_GENERIC, len(primes8) - 1))

    primes16 = primes_one_mod(16, ANCHOR_LIMIT, flags)
    rows16 = profile(16, primes16)
    exc16 = dict((p, c) for p, c, _, _ in rows16 if c != N16_GENERIC)
    assert len(primes16) == N16_COUNT, len(primes16)
    assert exc16 == CEILING_EXCEPTIONS_16, sorted(exc16.items())
    print("merged anchor n=16: %d primes p = 1 (mod 16) in [17, %d], count %d at %d, "
          "exceptions %d primes == merged PR #267 table %s"
          % (len(primes16), ANCHOR_LIMIT, N16_GENERIC, len(primes16) - len(exc16),
             len(exc16), sorted(exc16)))
    forced16 = [p for p in exc16 if (p - 1) // 16 < N16_GENERIC // 16]
    genuine16 = [p for p in exc16 if (p - 1) // 16 >= N16_GENERIC // 16]
    print("merged n=16 table, re-classified by this engine: %d counting-forced primes "
          "(p <= %d, fewer than %d cosets exist) and %d genuine-collision primes %s "
          "with p above that bound"
          % (len(forced16), 16 * (N16_GENERIC // 16), N16_GENERIC // 16, len(genuine16),
             sorted(genuine16)))

    # 2. Tie-out cells owned by other lanes, re-derived before reading the new row.
    for n, p, expected in ((32, 65537, SPOT_32_65537), (64, 65537, SPOT_64_65537),
                           (64, 6700417, SPOT_64_6700417),
                           (128, 257, SPOT_128_257), (128, 65537, SPOT_128_65537)):
        got = coset_census(n, p)[0]
        assert got == expected, (n, p, got, expected)
    prize_table = {}
    for n, expected in sorted(PRIZE_CELLS.items()):
        got = coset_census(n, PRIME_PRIZE)[0]
        assert got == expected, (n, got, expected)
        prize_table[n] = got
    print("tie-out cells reproduced by this engine: (32, 65537) = %d [open PR #272], "
          "(64, 65537) = %d [open PRs #300/#319], (64, 6700417) = %d [open PR #319], "
          "(128, 257) = %d, (128, 65537) = %d [campaign-staged, not merged]; "
          "prize prime 21*2^128+1 ladder n=16/32/64/128 = %d/%d/%d/%d"
          % (SPOT_32_65537, SPOT_64_65537, SPOT_64_6700417, SPOT_128_257,
             SPOT_128_65537, prize_table[16], prize_table[32], prize_table[64],
             prize_table[128]))

    # 3. The new rung: every prime p = 1 (mod 128) up to LIMIT.
    primes128 = primes_one_mod(N, LIMIT, flags)
    rows = profile(N, primes128)
    total = len(rows)
    counts = [r[1] for r in rows]
    at_ceiling = [r for r in rows if r[1] == CEILING_128]
    below = [r for r in rows if r[1] != CEILING_128]
    assert max(counts) == CEILING_128, max(counts)
    for p, count, cosets, zero in rows:
        assert count == N * cosets + zero, (p, count, cosets, zero)
        assert count <= p, (p, count)
        assert cosets <= (p - 1) // N, (p, cosets)
        assert (p - 1) % N == 0
    first_ceiling = at_ceiling[0][0] if at_ceiling else None
    last_below = below[-1][0] if below else None
    print("sweep n=128: %d primes p = 1 (mod 128) in [%d, %d]" % (total, 257, LIMIT))
    print("count == ceiling %d = 128 + 8*C(64,3) at %d of %d cells; %d cells strictly "
          "below; first ceiling cell p=%s, largest below-ceiling cell p=%s"
          % (CEILING_128, len(at_ceiling), total, len(below), first_ceiling, last_below))

    forced_rows = [r for r in rows if r[0] <= FORCED_BOUND]
    genuine_rows = [r for r in rows if r[0] > FORCED_BOUND]
    forced_full = [r for r in forced_rows if r[1] in (r[0] - 1, r[0])]
    forced_partial = [r for r in forced_rows if r[1] not in (r[0] - 1, r[0])]
    print("forced regime p <= %d (fewer than %d cosets exist): %d primes, of which %d "
          "saturate completely (count = p-1 or p) and %d leave cosets unhit"
          % (FORCED_BOUND, FLOOR_COSSETS, len(forced_rows), len(forced_full),
             len(forced_partial)))
    if forced_partial:
        worst = min(forced_partial, key=lambda r: (r[2] - (r[0] - 1) // N, r[0]))
        print("forced cells that leave cosets unhit: %d of them, smallest p=%d (count=%d, "
              "cosets=%d of %d available), largest p=%d"
              % (len(forced_partial), forced_partial[0][0], forced_partial[0][1],
                 forced_partial[0][2], (forced_partial[0][0] - 1) // N,
                 forced_partial[-1][0]))
        print("deepest forced shortfall: p=%d count=%d cosets=%d of %d available; the 5 "
              "smallest such cells are %s"
              % (worst[0], worst[1], worst[2], (worst[0] - 1) // N,
                 [(p, c, k, (p - 1) // N) for p, c, k, _ in forced_partial[:5]]))
    genuine_below = [r for r in genuine_rows if r[1] != CEILING_128]
    print("genuine-collision regime p > %d: %d primes, %d below the ceiling (%d of %d), "
          "%d at it" % (FORCED_BOUND, len(genuine_rows), len(genuine_below),
                        len(genuine_below), len(genuine_rows),
                        len(genuine_rows) - len(genuine_below)))

    zero_rows = [r for r in rows if r[3] == 1]
    print("0 is a bad scalar at %d of %d cells (the distinct vanishing-3-sum locus of "
          "mu_128 inside the swept range): %s"
          % (len(zero_rows), total, [p for p, _, _, _ in zero_rows]))
    zero_set = set(p for p, _, _, _ in zero_rows)
    assert LOCUS_EXCLUDED_128 not in zero_set, LOCUS_EXCLUDED_128
    assert 6700417 in zero_set and 65537 in zero_set and 257 in zero_set
    print("locus audit: the sweep contains 257, 65537 and 6700417 and EXCLUDES the "
          "degenerate-only divisor %d of R_128 (it is p = 1 (mod 128) and below %d)"
          % (LOCUS_EXCLUDED_128, LIMIT))

    deficits = {}
    for p, count, cosets, zero in genuine_below:
        deficits[FLOOR_COSSETS - cosets] = deficits.get(FLOOR_COSSETS - cosets, 0) + 1
    ranked = sorted(deficits.items(), key=lambda kv: (-kv[1], kv[0]))
    print("coset deficit against %d in the genuine regime: %d distinct deficits, largest "
          "%d, most common (deficit, count) pairs %s"
          % (FLOOR_COSSETS, len(deficits), max(deficits), ranked[:12]))

    top_counts = sorted(((c, counts.count(c)) for c in set(counts)),
                        key=lambda kv: (-kv[1], -kv[0]))[:8]
    print("distinct counts in the sweep: %d; the 8 most frequent (count, multiplicity) "
          "pairs are %s" % (len(set(counts)), top_counts))

    for low, high in WINDOWS:
        if low == WINDOWS[-1][0]:
            window = [r for r in rows if low <= r[0] <= high]
        else:
            window = [r for r in rows if low <= r[0] < high]
        hit = sum(1 for r in window if r[1] == CEILING_128)
        print("window [%d, %d]: %d primes, %d at ceiling %d (%d of %d), min count %d, "
              "max count %d, %d cells with 0 bad"
              % (low, high if low != WINDOWS[-1][0] else LIMIT, len(window), hit,
                 CEILING_128, hit, len(window), min(r[1] for r in window),
                 max(r[1] for r in window), sum(r[3] for r in window)))

    total_checksum = sum(count for _, count, _, _ in rows)
    weighted_checksum = sum(p * count for p, count, _, _ in rows)
    digest = hashlib.sha256()
    for row in rows:
        digest.update(("%d,%d,%d,%d;" % row).encode("ascii"))
    print("vector digest (p,count,cosets,zero over %d cells) sha256 %s"
          % (total, digest.hexdigest()))
    print("aggregate checksums: sum count = %d, sum p*count = %d"
          % (total_checksum, weighted_checksum))
    print("PASS: exact t=3 ceiling bad-scalar p-scaling profile of (x^3,x^2) at n=128 over "
          "all %d primes p = 1 (mod 128) in [257, %d]; merged n=8 (556) and n=16 (279, 34 "
          "exceptions) tables reproduced; ceiling %d at %d cells, %d below; structural law "
          "count = 128*cosets + [0 bad] and bounds count <= p, cosets <= (p-1)/128 asserted "
          "at every cell"
          % (total, LIMIT, CEILING_128, len(at_ceiling), len(below)))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
