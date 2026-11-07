#!/usr/bin/env python3
"""Exact ``t = 3`` ceiling census of the column ``b = n - 1``, pushed to the high rungs.

The ``t = 3`` ceiling monomial-pencil census on ``mu_n`` has one pencil whose count is
independent of the prime: this probe's companion (the published ``(x^2, x^(n-1))`` closed
form) measures ``count(x^2, x^(n-1)) = n`` at every tested prime.  That companion prints
the *whole column* ``b = n - 1`` only at ``n = 64`` and ``n = 128`` over the Fermat prime
``65537`` (two integers per column are pinned here and reproduced first).  This probe
pushes the same column two rungs higher and one prime regime over:

* rung coverage: ``n = 8, 16, 32, 64, 128, 256, 512`` (``n = 64, 128`` at ``65537`` are
  reproduced from the published integers, not re-derived);
* prime coverage: the Fermat prime ``65537`` (small regime) and the prize-scale Proth
  prime ``21*2^128+1`` (large regime), plus the Proth family ``k = 111, 123`` for the
  columns ``n = 64, 128`` to test whether the whole vector, not just the closed-form
  cell, is the same at all three.

Everything is exact integer arithmetic, stdlib only, deterministic; every printed claim
is hard-asserted and the script exits ``0`` only on ``PASS``.

Reproduced first (merged tree, ``scripts/probes/probe_order16_weight13_spectrum.py`` and
``scripts/probes/probe_n16_below_ceiling_max.py``): the ``(x^3, x^2)`` ceiling count at
``n = 8`` is ``40`` at every prime ``p = 1 (mod 8)`` in ``[17, 20000]`` except ``17``
(``16``), and at ``n = 16`` it is ``464`` at ``245`` of the ``279`` primes
``p = 1 (mod 16)`` in ``[17, 20000]`` with the other ``34`` exactly the merged exception
table; both are recomputed here through the shape/coset engine used below.

Structural laws read off the 14 primary columns (7 rungs x 2 regimes), asserted pencil by
pencil and printed instead of the raw ``a``-lists, so the transcript stays short:

* ``L-min``: the column minimum ``1`` is attained exactly at ``a in {0, 1, n-1}`` -- 14 of
  14 columns, both regimes;
* ``L-countn``: the closed-form value ``n`` is attained exactly at ``a = 2`` -- 14 of 14
  columns, both regimes;
* ``L-max``: the column maximum is attained exactly at ``a = 6 (mod 8)`` with
  ``a != 30 (mod 32)`` -- 7 of 7 columns over the prize prime, and only 2 of 7 at
  ``65537`` (``n = 8, 16``, where the two regimes share the whole vector);
* ``L-zero``: ``0`` lies in the bad set exactly at ``a = 0 or 1 (mod 4)`` -- 7 of 7 columns
  over the prize prime, 3 of 7 at ``65537``.

Where a set has no residue-class description at modulus ``<= 256`` the probe prints its
tally and points at the vector digest instead of the list; each digest is pinned to the
2026-11-02T10:05Z run of the uncompacted script, so the compaction cannot hide a change of
data.

Scope, read before citing.  This is a finite-field census slice: the ``t = 3`` ceiling
bad-scalar count of the ``n`` pencils of ONE column of the monomial-pencil census, at the
listed rungs and the listed primes, on the smooth domain ``mu_n`` of the dimension-two
code of affine words.  It is not a theorem in ``n`` or ``p``, not a statement about any
other column or row, not about ``t >= 4``, not about the global maximum of any census, not
about the production regime ``n = 2^30 / 2^32``, not about ``delta*``, and not about the
prize.  The column values at ``n <= 256`` over the prize prime lie inside the full
``n = 256`` census of this campaign's open PR #341 and the closed-form cell lies inside
the open PR #351; nothing here modifies a theorem, definition, ``DISPROOF_LOG`` entry, CI
file or toolchain.
"""

import hashlib
import time
from math import gcd, isqrt

LIMIT = 20_000
FERMAT = 65537
PRIZE_EXP = 128
PRIZE_K = (21, 111, 123)

# Rungs whose full column is computed here.  64 and 128 at 65537 are recomputed as well,
# because their published summary integers are the anchor for the extension.
COLUMN_RUNGS_FERMAT = (8, 16, 32, 64, 128, 256, 512)
COLUMN_RUNGS_PRIZE = (8, 16, 32, 64, 128, 256, 512)
COLUMN_RUNGS_PROTH_FAMILY = (64, 128)

# Published column summaries being extended (this campaign's open closed-form probe):
# column b = n-1 at p = 65537 -> the a-values at count n, column min, max, sum.
PUBLISHED_COLUMNS = {
    64: ((2,), 1, 30784, 1127669),
    128: ((2,), 1, 65537, 6885189),
}

# Merged PR #264 / #267 integers for the (x^3, x^2) ceiling count, recomputed here.
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

# The exact column vectors computed by the 2026-11-02 run of this probe, pinned by
# sha256 of the comma-separated count list.  The compaction of the transcript (the
# a-lists below are replaced by residue-class descriptions plus tallies) must not
# change a single count, so every column re-asserts its digest against this table.
PINNED_VECTOR_DIGESTS = {
    (8, "65537"): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, "65537"): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, "65537"): "3cce569863d7fdac3b3c966abcb1c1344bbe0419121e58bdfadb3f0bea11c961",
    (64, "65537"): "69f3e4c5416969ea428cf7fb0e96abd83ba6f6fc3ea11a9932313dfe6d5dfa1c",
    (128, "65537"): "5630704e234513e22d52b9d06f0bb46c3905869e5d675ec99f2194f2be3a8211",
    (256, "65537"): "238075666216e34ee9b077a22933f0063e4b64c7e35a4a88440c4ba8e5af4f81",
    (512, "65537"): "db7cd7e9bc2c5026039833dd18814db852a0463399564467d7f2e526bf5d1222",
    (8, "21*2^128+1"): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, "21*2^128+1"): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, "21*2^128+1"): "a9cce9cbf427e0f50fc3bb15266af206925552ceea154b856f98cc9801b65df5",
    (64, "21*2^128+1"): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
    (128, "21*2^128+1"): "baa6b0809122b4350b40d6482ba73974afe41e24b2d5855ccb55a76c13d8a5fb",
    (256, "21*2^128+1"): "d1aefd564a8c61afbd68dd21799aa14fea01efba79b8e0cd18542d6b25db213a",
    (512, "21*2^128+1"): "3d7c67d77a4235173b9bf2819d651258951048592c2262bb2c3b034e42989e34",
    (64, "111*2^128+1"): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
    (64, "123*2^128+1"): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
    (128, "111*2^128+1"): "baa6b0809122b4350b40d6482ba73974afe41e24b2d5855ccb55a76c13d8a5fb",
    (128, "123*2^128+1"): "baa6b0809122b4350b40d6482ba73974afe41e24b2d5855ccb55a76c13d8a5fb",
}
PINNED_COMBINED_DIGEST = (
    "824a45fd5c7ca2ce8262f6bdda7d9e4cc8dc2d5874cd2239ec73d67d4e81be64")


def class_form(n, members):
    """Residue-class cut-outs of the set: (M, classes) for every M | n, M <= 256."""
    members = sorted(members)
    forms = []
    for mod in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        if n % mod:
            continue
        classes = sorted({a % mod for a in members})
        if sorted(a for a in range(n) if a % mod in classes) == members:
            forms.append((mod, classes))
    return forms


SHORT_CLASSES = 8


def describe(n, members, digest):
    """Compact exact description of a subset of {0, ..., n-1}.

    Prefers the fewest printed residue classes, on the set or on its complement, and
    refuses to print a class list no shorter than the set it replaces.
    """
    members = sorted(members)
    if not members:
        return f"0 of {n} pencils (empty)"
    if len(members) == 1:
        return f"1 of {n} pencils, a = {members[0]}"
    if members == sorted({0, 1, n - 1}):
        return f"3 of {n} pencils, a in {{0, 1, n-1}}"
    forms = class_form(n, members)
    if forms:
        mod, classes = min(forms, key=lambda fc: (len(fc[1]), fc[0]))
        if len(classes) <= SHORT_CLASSES:
            return (f"{len(members)} of {n} pencils = "
                    f"{{a : a mod {mod} in {classes}}}")
    complement = [a for a in range(n) if a not in set(members)]
    cforms = class_form(n, complement)
    if cforms:
        mod, classes = min(cforms, key=lambda fc: (len(fc[1]), fc[0]))
        if len(classes) <= SHORT_CLASSES:
            return (f"{len(members)} of {n} pencils, all except "
                    f"{{a : a mod {mod} in {classes}}}")
    return (f"{len(members)} of {n} pencils, no residue-class description shorter than "
            f"the set (pinned losslessly by the vector sha256 {digest[:12]})")


LAW_NAMES = ("min-at-0-1-n-1", "count=n-only-at-2",
             "max-at-a=6-mod-8-excl-30-mod-32",
             "zero-in-bad-exactly-at-a=0-or-1-mod-4")


def law_string(laws):
    return "laws " + " ".join(f"{name}={'HOLDS' if laws[name] else 'FAILS'}"
                              for name in LAW_NAMES)


def column_laws(n, counts, profile, maximum, digest):
    """The four structural laws of a column, each with an exact verdict."""
    minset = [a for a in range(n) if counts[a] == 1]
    maxset = [a for a in range(n) if counts[a] == maximum]
    zeroset = [a for a in range(n) if profile[a][2]]
    exact_n = sorted(a for a in range(n) if counts[a] == n)
    laws = {
        "min-at-0-1-n-1": minset == sorted({0, 1, n - 1}),
        "count=n-only-at-2": exact_n == [2],
        "max-at-a=6-mod-8-excl-30-mod-32":
            maxset == [a for a in range(n) if a % 8 == 6 and a % 32 != 30],
        "zero-in-bad-exactly-at-a=0-or-1-mod-4":
            zeroset == [a for a in range(n) if a % 4 in (0, 1)],
    }
    return laws, {"min": minset, "max": maxset, "zero": zeroset, "exact_n": exact_n}


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
    """k*2^exponent + 1 with Proth's theorem certified by an explicit witness."""
    value = k * (2 ** exponent) + 1
    assert k % 2 == 1 and k < 2 ** exponent, (k, exponent)
    for witness in range(2, 64):
        if pow(witness, (value - 1) // 2, value) == value - 1:
            return value, witness
    raise AssertionError(f"no Proth witness below 64 for k={k}")


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


class Shapes:
    """The normalised-shape engine: triple shapes and the closed-form ``h`` rows."""

    def __init__(self, n, p):
        self.n, self.p = n, p
        generator = order_element(p, n)
        self.generator = generator
        xs = [pow(generator, exponent, p) for exponent in range(n)]
        assert len(set(xs)) == n
        self.xs = xs
        pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
        self.pairs = pairs
        self.ys = [xs[u] for u, v in pairs]
        self.zs = [xs[v] for u, v in pairs]
        self.diff = [(y - z) % p for y, z in zip(self.ys, self.zs)]
        self.zm1 = [(z - 1) % p for z in self.zs]
        self.ym1 = [(1 - y) % p for y in self.ys]
        denom = [((1 - y) * (1 - z) * (y - z)) % p
                 for y, z in zip(self.ys, self.zs)]
        assert all(value for value in denom), "distinct 1, y, z required"
        self.inv_denom = batch_inverse(denom, p)

    def row(self, exponent):
        """h_(exponent-2)(1, y, z) on every shape, via the closed form."""
        p = self.p
        diff, zm1, ym1, inv = self.diff, self.zm1, self.ym1, self.inv_denom
        ys, zs = self.ys, self.zs
        return [((diff[i] + pow(ys[i], exponent, p) * zm1[i]
                  + pow(zs[i], exponent, p) * ym1[i]) % p) * inv[i] % p
                for i in range(len(ys))]

    def t3(self, a, b, row_a=None, row_b=None):
        """(count, m, nonzero cosets hit, 0 bad) for the ceiling event of (a, b)."""
        p, n = self.p, self.n
        ha = self.row(a) if row_a is None else row_a
        hb = self.row(b) if row_b is None else row_b
        m = n // gcd((b - a) % n, n)
        inv_b = batch_inverse(hb, p)
        keys = set()
        add = keys.add
        for index, value in enumerate(hb):
            if value:
                add(pow((-ha[index] * inv_b[index]) % p, m, p))
        zero = 0 in keys
        cosets = len(keys) - (1 if zero else 0)
        return m * cosets + (1 if zero else 0), m, cosets, zero


def column(shapes):
    """Every count of the column b = n-1, keyed by a, with the m/zero profile."""
    n, p = shapes.n, shapes.p
    row_b = shapes.row(n - 1)
    counts = {}
    profile = {}
    for a in range(n):
        count, m, cosets, zero = shapes.t3(a, n - 1, row_b=row_b)
        counts[a] = count
        profile[a] = (m, cosets, zero)
    assert len(counts) == n
    return counts, profile


def summarise(counts, p):
    n = len(counts)
    values = [counts[a] for a in range(n)]
    minimum = min(values)
    maximum = max(values)
    total = sum(values)
    weighted = sum(a * counts[a] for a in range(n))
    exact_n = tuple(sorted(a for a in range(n) if counts[a] == n))
    at_ceiling = tuple(sorted(a for a in range(n) if counts[a] == p))
    top = sorted(((counts[a], a) for a in range(n)), reverse=True)[:6]
    digest = hashlib.sha256(
        ",".join(str(counts[a]) for a in range(n)).encode()).hexdigest()
    return {"min": minimum, "max": maximum, "sum": total, "weighted": weighted,
            "exact_n": exact_n, "at_ceiling": at_ceiling, "top": top, "digest": digest}


def label(p, prize_primes):
    for k, value in prize_primes.items():
        if p == value:
            return f"{k}*2^128+1"
    return str(p)


def main():
    start = time.time()
    print("t=3 ceiling column b = n-1 census at the high rungs", flush=True)
    prize_primes = {}
    for k in PRIZE_K:
        value, witness = proth_prime(k, PRIZE_EXP)
        prize_primes[k] = value
        assert k % 2 == 1 and k < 2 ** PRIZE_EXP
        assert pow(witness, (value - 1) // 2, value) == value - 1
        print(f"Proth certificate: {k}*2^128+1 is prime, k = {k} odd with k < 2^128 and "
              f"witness {witness} giving a^((p-1)/2) = -1, so Proth's theorem applies",
              flush=True)
    prize = prize_primes[21]
    assert (FERMAT - 1) % 512 == 0 and (prize - 1) % 1024 == 0

    # 1. Merged anchors recomputed through the same engine that runs the columns.
    n8 = primes_one_mod(8, LIMIT)
    assert len(n8) == N8_PRIME_COUNT, len(n8)
    split8 = []
    for p in n8:
        count = Shapes(8, p).t3(3, 2)[0]
        expected = N8_CEILING_EXCEPTIONS.get(p, N8_CEILING_DEFAULT)
        if count != expected:
            split8.append((p, count, expected))
    assert not split8, split8
    assert Shapes(8, 17).t3(3, 2)[0] == 16
    n16 = primes_one_mod(16, LIMIT)
    assert len(n16) == N16_PRIME_COUNT, len(n16)
    exceptions16 = []
    for p in n16:
        count = Shapes(16, p).t3(3, 2)[0]
        if count != N16_CEILING_DEFAULT:
            exceptions16.append((p, count))
    assert [p for p, _ in exceptions16] == sorted(N16_CEILING_EXCEPTIONS), exceptions16
    assert dict(exceptions16) == N16_CEILING_EXCEPTIONS
    assert Shapes(16, FERMAT).t3(3, 2)[0] == 464
    assert Shapes(16, prize).t3(3, 2)[0] == 464
    print(f"merged anchors reproduced by this engine: n=8 (x^3,x^2) ceiling "
          f"{N8_CEILING_DEFAULT} at all {N8_PRIME_COUNT} primes p = 1 (mod 8) in "
          f"[17, {LIMIT}] except {N8_CEILING_EXCEPTIONS}; n=16 {N16_CEILING_DEFAULT} at "
          f"{N16_PRIME_COUNT - len(N16_CEILING_EXCEPTIONS)} of {N16_PRIME_COUNT} primes "
          f"with the {len(N16_CEILING_EXCEPTIONS)} exceptions exactly the merged table, "
          f"and 464 at {FERMAT} and at 21*2^128+1", flush=True)

    # 2. The published column summaries being extended are recomputed first.
    for n, pinned in sorted(PUBLISHED_COLUMNS.items()):
        counts, _ = column(Shapes(n, FERMAT))
        summary = summarise(counts, FERMAT)
        assert (summary["exact_n"], summary["min"], summary["max"], summary["sum"]) == pinned, (
            n, summary, pinned)
        print(f"published column anchor n={n} p={FERMAT}: count = n at a in "
          f"{summary['exact_n']}, min {summary['min']}, max {summary['max']}, sum "
          f"{summary['sum']} -- matches the pinned integers {pinned}", flush=True)

    # 3. The columns.
    vectors = {}
    law_rows = []
    for n in COLUMN_RUNGS_FERMAT:
        counts, profile = column(Shapes(n, FERMAT))
        summary = summarise(counts, FERMAT)
        vectors[(n, FERMAT)] = counts
        assert summary["exact_n"] and 2 in summary["exact_n"], (n, summary)
        assert counts[2] == n and counts[n - 1] == 1 and counts[0] == 1 and counts[1] == 1
        assert summary["min"] == 1
        for a in range(n):
            m, cosets, zero = profile[a]
            assert counts[a] == m * cosets + (1 if zero else 0), (n, a, profile[a])
            assert counts[a] % m == (1 if zero else 0), (n, a, counts[a], m, zero)
        top_counts = {}
        for a in range(n):
            top_counts[counts[a]] = top_counts.get(counts[a], 0) + 1
        assert summary["digest"] == PINNED_VECTOR_DIGESTS[(n, "65537")], (n, summary["digest"])
        laws, sets = column_laws(n, counts, profile, summary["max"], summary["digest"])
        assert laws["min-at-0-1-n-1"] and laws["count=n-only-at-2"], (n, laws)
        print(f"column b = {n - 1} at p = {FERMAT} (n={n}): {n} pencils, min "
              f"{summary['min']} at a in {describe(n, sets['min'], summary['digest'])}, "
              f"max {summary['max']} at a in {describe(n, sets['max'], summary['digest'])}, "
              f"count = n at a in {describe(n, sets['exact_n'], summary['digest'])}, "
              f"count = p at a in "
              f"{describe(n, summary['at_ceiling'], summary['digest'])}, sum "
              f"{summary['sum']}, weighted {summary['weighted']}, distinct values "
              f"{len(top_counts)}, top "
              f"{sorted(top_counts.items(), reverse=True)[:5]}, bad set contains 0: "
              f"{describe(n, sets['zero'], summary['digest'])}; {law_string(laws)}; "
              f"vector sha256 {summary['digest']}", flush=True)
        law_rows.append(("65537", n, laws))
        assert profile[2][2] is False and counts[2] == n
    for n in COLUMN_RUNGS_PRIZE:
        counts, profile = column(Shapes(n, prize))
        summary = summarise(counts, prize)
        vectors[(n, prize)] = counts
        assert counts[2] == n and summary["min"] == 1
        assert not summary["at_ceiling"], (n, summary)
        for a in range(n):
            m, cosets, zero = profile[a]
            assert counts[a] == m * cosets + (1 if zero else 0), (n, a, profile[a])
            assert counts[a] % m == (1 if zero else 0), (n, a, counts[a], m, zero)
        top_counts = {}
        for a in range(n):
            top_counts[counts[a]] = top_counts.get(counts[a], 0) + 1
        assert summary["digest"] == PINNED_VECTOR_DIGESTS[(n, "21*2^128+1")], (n, summary["digest"])
        laws, sets = column_laws(n, counts, profile, summary["max"], summary["digest"])
        assert all(laws.values()), (n, laws)
        print(f"column b = {n - 1} at p = 21*2^128+1 (n={n}): {n} pencils, min "
              f"{summary['min']} at a in {describe(n, sets['min'], summary['digest'])}, "
              f"max {summary['max']} at a in {describe(n, sets['max'], summary['digest'])}, "
              f"count = n at a in {describe(n, sets['exact_n'], summary['digest'])}, "
              f"sum {summary['sum']}, weighted {summary['weighted']}, distinct values "
              f"{len(top_counts)}, top "
              f"{sorted(top_counts.items(), reverse=True)[:5]}, bad set contains 0: "
              f"{describe(n, sets['zero'], summary['digest'])}; {law_string(laws)}; "
              f"vector sha256 {summary['digest']}", flush=True)
        law_rows.append(("21*2^128+1", n, laws))

    # 4. The same column at the other two Proth primes of the prize family.
    for n in COLUMN_RUNGS_PROTH_FAMILY:
        base = vectors[(n, prize)]
        for k in (111, 123):
            other = prize_primes[k]
            counts, _ = column(Shapes(n, other))
            vectors[(n, other)] = counts
            assert counts == base, n
            summary = summarise(counts, other)
            assert summary["digest"] == PINNED_VECTOR_DIGESTS[(n, f"{k}*2^128+1")], (n, k)
            print(f"column b = {n - 1} at p = {k}*2^128+1 (n={n}): identical to the "
                  f"21*2^128+1 column (all {n} entries), vector sha256 "
                  f"{summary['digest']}, sum {summary['sum']}", flush=True)

    # 5. Cross-regime agreement of the closed-form cell and the small rungs.
    for n in (8, 16, 32, 64, 128, 256, 512):
        assert vectors[(n, FERMAT)][2] == n == vectors[(n, prize)][2], n
    small_same = [n for n in (8, 16, 32)
                  if vectors[(n, FERMAT)] == vectors[(n, prize)]]
    print(f"closed-form cell count = n at a = 2 in every column of both regimes; the "
          f"whole column vector agrees between {FERMAT} and 21*2^128+1 exactly at "
          f"n in {small_same}", flush=True)

    total_digest = hashlib.sha256(
        "|".join(f"{n},{label(p, prize_primes)},"
                 + ",".join(str(vectors[(n, p)][a]) for a in range(n))
                 for (n, p) in sorted(vectors)).encode()).hexdigest()
    assert total_digest == PINNED_COMBINED_DIGEST, (total_digest, PINNED_COMBINED_DIGEST)
    for regime in ("65537", "21*2^128+1"):
        cells = [row for row in law_rows if row[0] == regime]
        for name in cells[0][2]:
            held = [row[1] for row in cells if row[2][name]]
            print(f"law {name} at p = {regime}: holds in {len(held)} of {len(cells)} "
                  f"columns, rung n = {tuple(held)}", flush=True)
    print(f"all columns: {len(vectors)} vectors, "
          f"{sum(len(v) for v in vectors.values())} entries, combined digest {total_digest}",
          flush=True)

    print(f"PASS: exact t=3 ceiling column b=n-1 census at n in "
          f"{tuple(sorted({n for n, _ in vectors}))} over "
          f"{FERMAT}, 21*2^128+1 and (n<=128) 111*2^128+1, 123*2^128+1; in both regimes "
          f"the value n is attained at exactly a = 2 and the value 1 at exactly "
          f"a in {{0, 1, n-1}} in all {len(law_rows)} columns; in the prize regime the "
          f"column maximum is attained exactly at a = 6 (mod 8) with a != 30 (mod 32) and "
          f"0 lies in the bad set exactly at a = 0 or 1 (mod 4), at all 7 rungs; every "
          f"vector digest is pinned to the 2026-11-02T10:05Z run; no theorem in n or "
          f"p, no t>=4, no global-maximum, no production-regime, no delta* or prize claim",
          flush=True)
    print(f"elapsed {time.time() - start:.1f}s", flush=True)


if __name__ == "__main__":
    main()
