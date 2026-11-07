#!/usr/bin/env python3
"""Independent crosscheck of the ``t = 3`` ceiling column ``b = n - 1`` census.

Four routes, none of which reuses the closed-form ``h`` row or the ``ratio^m`` field
exponentiation key of the main probe:

* Route A (literal triples, no shapes at all).  For every literal triple ``T`` of ``mu_n``
  the raw ``2 x 2`` elimination determinants are formed from the actual field values and the
  bad-scalar set is collected literally as ``{ -D_a(T) / D_b(T) : D_b(T) != 0 }``; the count
  is the size of that set -- no orbit formula, no dilation key.  Complete columns for
  ``n = 8, 16, 32, 64, 128`` over both primes.
* Route B (discrete-log indices at ``65537``).  A full primitive-root logarithm table of
  ``F_65537`` replaces every field exponentiation by integer arithmetic in ``Z/65536``: the
  rows come from cofactor-expanded ``3 x 3`` determinants (no denominator division, no
  closed form), a ratio is a sum and difference of table indices, and two ratios share a
  dilation orbit exactly when their indices are congruent modulo ``(p-1)/m``.  Complete
  columns for ``n = 128, 256, 512`` over ``65537``.
* Route C (keying-free explicit orbit union).  For pinned lists of ``a`` the bad set is
  built literally as the union of the sets ``{ r * nu : nu in mu_m }``, with no orbit key and
  no counting formula; the size of the union is printed as the count.  This is the only
  route run at ``n = 512`` over the prize prime, where an explicit union of the large orbits
  is affordable only for the pencils whose orbits are small.
* Route D (merged integers by the negated-3-sum semantics of the merged probes).  The
  ``(x^3, x^2)`` ceiling counts that the main probe takes as anchors are recomputed as the
  set of negated sums of three distinct elements of ``mu_8`` and ``mu_16`` over every prime
  of the merged scan ranges -- a subset-sum route with no ratio, no shape and no orbit.

The structural laws the main probe now prints in place of its ``a``-lists are recomputed
here from each route's own objects: route A reads ``0``-membership out of the literally
enumerated bad sets, route B out of its own ``D_a = 0`` predicate, and route C tests the
law membership of every sampled pencil against the published prize-regime maximum.

Stdlib only, deterministic, exact integer arithmetic.  It checks the same objects at the
same parameters and is compared with the main probe's saved stdout cell by cell by
``auto/audit_column_agreement.py``.  Same scope limits as the main probe: finite fields, the
listed rungs and primes, the ``t = 3`` ceiling census on the smooth domain ``mu_n`` -- not a
theorem in ``n`` or ``p``, not ``t >= 4``, not a global maximum, not the production regime,
not ``delta*``, not the prize.
"""

import hashlib
import time
from itertools import combinations
from math import gcd, isqrt

LIMIT = 20_000
FERMAT = 65537
PRIZE_EXP = 128

TRIPLE_RUNGS = (8, 16, 32, 64, 128)
LOG_RUNGS = (128, 256, 512)
ORBIT_SAMPLES = {
    64: (0, 1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 62, 63),
    128: (0, 1, 2, 3, 4, 6, 8, 16, 20, 32, 64, 126, 127),
    256: (0, 1, 2, 3, 4, 6, 8, 16, 32, 64, 128, 254, 255),
    512: (0, 1, 2, 6, 511),
}

# Column maxima over the prize prime as published by the main probe, used here only to
# test, pencil by pencil on the sampled a, which of them reach that maximum: the law
# says exactly the a = 6 (mod 8) with a != 30 (mod 32).
PRIZE_MAXIMA = {8: 40, 16: 464, 32: 4640, 64: 40512, 128: 337024,
                256: 2746624, 512: 22172160}
N8_CEILING_DEFAULT = 40
N8_CEILING_EXCEPTIONS = {17: 16}
N16_CEILING_DEFAULT = 464
N16_CEILING_EXCEPTIONS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
N8_PRIME_COUNT = 556
N16_PRIME_COUNT = 279


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


def primes_one_mod(p_mod, limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start:limit + 1:divisor] = b"\x00" * len(sieve[start:limit + 1:divisor])
    return [p for p in range(p_mod, limit + 1) if sieve[p] and p % p_mod == 1]


def proth_prime(k, exponent):
    value = k * (2 ** exponent) + 1
    assert k % 2 == 1 and k < 2 ** exponent, (k, exponent)
    for witness in range(2, 64):
        if pow(witness, (value - 1) // 2, value) == value - 1:
            return value, witness
    raise AssertionError(f"no Proth witness below 64 for k={k}")


def order_element(p, n):
    assert (p - 1) % n == 0
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def domain(n, p):
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n and xs[0] == 1
    return generator, xs


def digest(counts):
    n = len(counts)
    return hashlib.sha256(",".join(str(counts[a]) for a in range(n)).encode()).hexdigest()


def summary_line(counts):
    n = len(counts)
    exact_n = tuple(sorted(a for a in range(n) if counts[a] == n))
    return (f"min {min(counts.values())} max {max(counts.values())} sum "
            f"{sum(counts.values())} weighted {sum(a * c for a, c in counts.items())} "
            f"count=n at a in {exact_n} digest {digest(counts)}")


LAWS = ("min-at-0-1-n-1", "count=n-only-at-2",
        "max-at-a=6-mod-8-excl-30-mod-32", "zero-in-bad-exactly-at-a=0-or-1-mod-4")


def law_verdicts(n, counts, zeros):
    """The four column laws, evaluated on a literally-enumerated column.

    ``zeros`` is the set of ``a`` whose bad set contains ``0``, obtained from the route's
    own construction (literal ``0`` in the enumerated set, or the route's own zero
    predicate), never from the main probe's profile.
    """
    maximum = max(counts[a] for a in range(n))
    minset = sorted(a for a in range(n) if counts[a] == 1)
    maxset = sorted(a for a in range(n) if counts[a] == maximum)
    exact_n = sorted(a for a in range(n) if counts[a] == n)
    verdicts = {
        "min-at-0-1-n-1": minset == sorted({0, 1, n - 1}),
        "count=n-only-at-2": exact_n == [2],
        "max-at-a=6-mod-8-excl-30-mod-32":
            maxset == [a for a in range(n) if a % 8 == 6 and a % 32 != 30],
        "zero-in-bad-exactly-at-a=0-or-1-mod-4":
            sorted(set(zeros)) == [a for a in range(n) if a % 4 in (0, 1)],
    }
    return verdicts, maximum, maxset


def law_string(verdicts):
    return "laws " + " ".join(f"{name}={'HOLDS' if verdicts[name] else 'FAILS'}"
                              for name in LAWS)


# ---------------------------------------------------------------------------
# Route A: literal triples of mu_n, raw 2x2 elimination determinants, |set|.
# ---------------------------------------------------------------------------

def route_a_column(n, p):
    """{a: |bad set|} for the whole column b = n-1 by literal triple enumeration."""
    b = n - 1
    _generator, xs = domain(n, p)
    powers = [[pow(x, e, p) for x in xs] for e in range(n)]
    rows_b = powers[b]
    triples = []
    for i, j, k in combinations(range(n), 3):
        a11 = (rows_b[j] - rows_b[i]) % p
        a12 = (xs[i] - xs[j]) % p
        a21 = (rows_b[k] - rows_b[i]) % p
        a22 = (xs[i] - xs[k]) % p
        det_second = (a11 * a22 - a12 * a21) % p
        if det_second:
            triples.append((i, j, k, a12, a22, pow(det_second, -1, p)))
    count_triples = n * (n - 1) * (n - 2) // 6
    denom_nonzero = len(triples)
    counts = {}
    zeros = []
    for a in range(n):
        row_a = powers[a]
        bad = set()
        for i, j, k, a12, a22, det_inv in triples:
            b1 = (row_a[j] - row_a[i]) % p
            b2 = (row_a[k] - row_a[i]) % p
            bad.add(((-b1) * a22 + a12 * b2) % p * det_inv % p)
        counts[a] = len(bad)
        if 0 in bad:
            zeros.append(a)
    assert denom_nonzero <= count_triples
    return counts, denom_nonzero, count_triples - denom_nonzero, zeros


# ---------------------------------------------------------------------------
# Route B: discrete-log indices over F_65537 and cofactor 3x3 determinants.
# ---------------------------------------------------------------------------

def primitive_root(p):
    """p - 1 = 2^k here, so w is primitive iff w^((p-1)/2) = -1."""
    for candidate in range(2, p):
        if pow(candidate, (p - 1) // 2, p) == p - 1:
            assert pow(candidate, p - 1, p) == 1
            return candidate
    raise AssertionError(f"no primitive root below {p}")


def log_table(p, root):
    logs = [-1] * p
    value = 1
    for exponent in range(p - 1):
        logs[value] = exponent
        value = value * root % p
    assert value == 1 and logs[1] == 0 and logs[p - 1] == (p - 1) // 2
    assert sum(1 for entry in logs[1:] if entry >= 0) == p - 1
    return logs


def det_row(y, z, y_top, z_top):
    """det [[1,1,1],[1,y,z],[1,y_top,z_top]] by cofactor expansion."""
    return ((y * z_top - z * y_top) - (z_top - z) + (y_top - y))


def route_b_column(n, p, logs):
    """Column b = n-1 over F_p by log indices and literal 3x3 determinants."""
    assert p == FERMAT and n < p
    _generator, xs = domain(n, p)
    pows = [[pow(x, e, p) for x in xs] for e in range(n)]
    log_minus_one = logs[p - 1]
    mod_full = p - 1
    counts = {}
    zeros = []
    for a in range(n):
        m = n // gcd((n - 1 - a) % n, n)
        modulus = mod_full // m
        keys = set()
        zero_bad = False
        for u in range(1, n):
            y = xs[u]
            y_b = pows[n - 1][u]
            y_a = pows[a][u]
            for v in range(u + 1, n):
                z = xs[v]
                d_b = det_row(y, z, y_b, pows[n - 1][v]) % p
                if not d_b:
                    continue
                d_a = det_row(y, z, y_a, pows[a][v]) % p
                if not d_a:
                    zero_bad = True
                    continue
                index = (logs[d_a] + log_minus_one - logs[d_b]) % mod_full
                keys.add(index % modulus)
        counts[a] = m * len(keys) + (1 if zero_bad else 0)
        if zero_bad:
            zeros.append(a)
    return counts, zeros


# ---------------------------------------------------------------------------
# Route C: keying-free explicit union of dilation orbits.
# ---------------------------------------------------------------------------

def route_c_count(n, p, a):
    b = n - 1
    generator, xs = domain(n, p)
    m = n // gcd((b - a) % n, n)
    step = pow(generator, n // m, p)
    subgroup = []
    value = 1
    for _ in range(m):
        subgroup.append(value)
        value = value * step % p
    assert len(set(subgroup)) == m and value == 1
    powers_a = [pow(x, a, p) for x in xs]
    powers_b = [pow(x, b, p) for x in xs]
    union = set()
    for u in range(1, n):
        y = xs[u]
        for v in range(u + 1, n):
            z = xs[v]
            d_b = det_row(y, z, powers_b[u], powers_b[v]) % p
            if not d_b:
                continue
            d_a = det_row(y, z, powers_a[u], powers_a[v]) % p
            if not d_a:
                union.add(0)
                continue
            ratio = (-d_a) * pow(d_b, -1, p) % p
            for element in subgroup:
                union.add(ratio * element % p)
    return len(union), m, (0 in union)


# ---------------------------------------------------------------------------
# Route D: merged anchors by negated triple sums (no ratio, no shape, no orbit).
# ---------------------------------------------------------------------------

def negated_triple_sum_count(n, p):
    _generator, xs = domain(n, p)
    return len({(-(xs[i] + xs[j] + xs[k])) % p
                for i, j, k in combinations(range(n), 3)})


def main():
    start = time.time()
    print("independent crosscheck of the t=3 ceiling column b = n-1 census", flush=True)
    prize, prize_witness = proth_prime(21, PRIZE_EXP)
    assert pow(prize_witness, (prize - 1) // 2, prize) == prize - 1
    print(f"route D: prize prime 21*2^128+1 certified by Proth, witness "
          f"{prize_witness}", flush=True)

    n8_primes = primes_one_mod(8, LIMIT)
    assert len(n8_primes) == N8_PRIME_COUNT
    split8 = []
    for p in n8_primes:
        count = negated_triple_sum_count(8, p)
        if count != N8_CEILING_DEFAULT:
            split8.append((p, count))
    assert dict(split8) == N8_CEILING_EXCEPTIONS, split8
    n16_primes = primes_one_mod(16, LIMIT)
    assert len(n16_primes) == N16_PRIME_COUNT
    exceptions16 = []
    for p in n16_primes:
        count = negated_triple_sum_count(16, p)
        if count != N16_CEILING_DEFAULT:
            exceptions16.append((p, count))
    assert dict(exceptions16) == N16_CEILING_EXCEPTIONS, exceptions16
    assert negated_triple_sum_count(16, FERMAT) == 464
    assert negated_triple_sum_count(16, prize) == 464
    print(f"route D: negated distinct 3-sums of mu_8 over all {N8_PRIME_COUNT} primes "
          f"p = 1 (mod 8) in [17, {LIMIT}] give {N8_CEILING_DEFAULT} except {split8}; "
          f"mu_16 over all {N16_PRIME_COUNT} primes p = 1 (mod 16) give "
          f"{N16_CEILING_DEFAULT} with the {len(exceptions16)} exceptions exactly the "
          f"merged table, and {N16_CEILING_DEFAULT} at {FERMAT} and at 21*2^128+1",
          flush=True)

    for n in TRIPLE_RUNGS:
        for p, name in ((FERMAT, str(FERMAT)), (prize, "21*2^128+1")):
            stage = time.time()
            counts, nonzero, degenerate, zeros = route_a_column(n, p)
            assert counts[2] == n
            verdicts, maximum, maxset = law_verdicts(n, counts, zeros)
            assert verdicts["min-at-0-1-n-1"], (n, name)
            assert verdicts["count=n-only-at-2"], (n, name)
            if name == "21*2^128+1":
                assert verdicts["max-at-a=6-mod-8-excl-30-mod-32"], (n, maxset)
                assert verdicts["zero-in-bad-exactly-at-a=0-or-1-mod-4"], (n, zeros)
            print(f"route A n={n} p={name}: all {n} pencils of the column b={n - 1} by "
                  f"literal triples ({nonzero} with D_b nonzero, {degenerate} degenerate), "
                  + summary_line(counts) + f" maximizers {maxset} zero-in-bad count "
                  f"{len(zeros)}; {law_string(verdicts)}" + f" ({time.time() - stage:.0f}s)",
                  flush=True)

    root = primitive_root(FERMAT)
    logs = log_table(FERMAT, root)
    assert logs[pow(root, 3, FERMAT)] == 3
    for n in LOG_RUNGS:
        stage = time.time()
        counts, zeros = route_b_column(n, FERMAT, logs)
        assert counts[2] == n
        verdicts, maximum, maxset = law_verdicts(n, counts, zeros)
        assert verdicts["min-at-0-1-n-1"], n
        assert verdicts["count=n-only-at-2"], n
        print(f"route B n={n} p={FERMAT}: {n} pencils by literal 3x3 determinants and "
              f"index arithmetic mod (p-1)/m, " + summary_line(counts)
              + f" maximizer count {len(maxset)} zero-in-bad count {len(zeros)}; "
              f"{law_string(verdicts)}" + f" ({time.time() - stage:.0f}s)", flush=True)

    for n, sample in sorted(ORBIT_SAMPLES.items()):
        for p, name in ((FERMAT, str(FERMAT)), (prize, "21*2^128+1")):
            if n == 512 and p == FERMAT:
                continue  # covered in full by route B at this prime
            parts = []
            for a in sample:
                size, m, zero_member = route_c_count(n, p, a)
                if name == "21*2^128+1":
                    assert zero_member == (a % 4 in (0, 1)), (n, a, zero_member)
                    assert (size == PRIZE_MAXIMA[n]) == (a % 8 == 6 and a % 32 != 30), (
                        n, a, size, PRIZE_MAXIMA[n])
                parts.append(f"a={a}:{size}(m={m},0-in-bad={zero_member})")
            print(f"route C n={n} p={name}: explicit orbit unions, no key, no formula -> "
                  + " ".join(parts)
                  + (f"; prize-law membership on {len(sample)} sampled pencils "
                     f"(max-at-6-mod-8-excl-30-mod-32 and zero-in-bad-at-0-or-1-mod-4) "
                     f"HOLDS" if name == "21*2^128+1" else ""), flush=True)

    print("PASS: independent routes agree on the column b=n-1 census -- literal-triple "
          "|set| columns at n in (8, 16, 32, 64, 128) over both primes, log-index "
          "determinant columns at n in (128, 256, 512) over 65537, keying-free orbit "
          "unions on the pinned a-lists, merged anchors by the negated-3-sum route at "
          "556 + 279 + 2 primes; the four column laws (min at 0,1,n-1; count=n only at "
          "a=2; prize-regime max at a=6 mod 8 excluding a=30 mod 32; prize-regime 0 in "
          "bad exactly at a=0 or 1 mod 4) are recomputed here from each route's own "
          "sets, with zero-membership taken from the literal sets rather than any "
          "profile",
          flush=True)
    print(f"elapsed {time.time() - start:.1f}s", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
