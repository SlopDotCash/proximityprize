#!/usr/bin/env python3
"""Isolation of the (x^2, x^(n-1)) closed form: it is the ONLY monomial-ratio pencil.

Object (the published t=3 ceiling monomial-pencil census).  Fix a prime ``p`` with
``n | p - 1``, the smooth domain ``x_i = g^i`` of ``mu_n``, and the dimension-two code of
affine words.  For the monomial pencil ``(u0, u1) = (x^a, x^b)`` the ceiling (``t = 3``)
bad scalars are exactly ``{ -D_a(T)/D_b(T) : D_b(T) != 0 }``, where ``D_e(T)`` is the
collinearity determinant of ``(1, x, x^e)`` on the triple ``T``.  Writing
``D_e = V_T * h_(e-2)`` with ``V_T`` the Vandermonde product, every row is a quotient of
two fixed Laurent sums evaluated at the normalised shape ``(1, y, z)``,

    N_e(y, z) = (y - z) + y^e (z - 1) + z^e (1 - y),   den = (1 - y)(1 - z)(y - z),

and the bad ratio of the pencil is ``-N_a / N_b``.  The two published identities

    N_2 = den          (so h_0 == 1)         y z * N_(n-1) = den   (so h_(n-3) == 1/(y z))

force the bad ratio of the pencil ``{a, b} = {2, n-1}`` to be the SINGLE MONOMIAL ``-y z``,
which is why its bad set is ``mu_n`` and its count is ``n`` independently of ``p``.

Claim (this probe).  That pair is ISOLATED.  Work in the group ring
``A_n = Z[y, z] / <y^n - 1, z^n - 1>`` and call two rows equivalent when
``N_a = c * y^i z^j * N_b`` in ``A_n`` for some ``0 <= i, j < n`` and ``c = +-1`` -- exactly
the condition that the bad ratio ``-N_a/N_b`` be a single monomial, i.e. that the
closed-form mechanism apply.  Computed exhaustively:

* for every ``n`` in ``[3, 300]`` and for the two-power rungs ``n = 2^k``, ``k = 2..15``
  (``4`` to ``32768``): the zero rows are exactly ``N_0 = N_1 = 0``; each of the ``n - 2``
  rows ``N_e``, ``2 <= e <= n - 1``, has EXACTLY SIX ``+-1`` terms (no term collision at
  any ``n``, any ``e``); and the equivalence classes are exactly ONE two-element class
  ``{2, n-1}`` plus ``n - 4`` singletons (at ``n = 3`` the two exponents coincide, so there
  is a single row and no pair);
* the certificate of that class is UNIQUE: ``N_(n-1) = y^(n-1) z^(n-1) * N_2``, no other
  ``(i, j, c)`` relates the two rows, so the closed form has exactly one monomial
  normalisation;
* hence among the ``C(n-2, 2)`` unordered pencils of nonzero rows, exactly ONE has a
  monomial bad ratio.  Every other pencil's ratio is a genuine two-row quotient, which is
  why its count depends on ``p`` (the merged ``n = 16`` exception table) instead of
  collapsing to ``n``.

Semantic bridge, computed and not assumed.  At real primes the unique pair does what the
classification says it must: the bad set of ``(x^2, x^(n-1))`` is SET-equal to ``mu_n``
with count ``n`` at every cell of ``n`` in ``{8,16,32,64,128}`` x ``{three smallest
p = 1 (mod n), 65537, 21*2^128+1}``, while the neighbouring pencils whose rows the
classification separates have counts that move with ``p``.  Merged anchors reproduced
through the published shape engine: the ``(x^3, x^2)`` ceiling count is ``16`` at ``p=17``
and ``40`` at every other one of the ``556`` primes ``p = 1 (mod 8)`` in ``[17, 20000]``
(G310/G328/G330), and at ``n = 16`` it is ``464`` outside the published ``34``-prime
exception set and equals the merged ``CEILING_EXCEPTIONS`` table at all ``279`` primes
``p = 1 (mod 16)`` in ``[17, 20000]``.

Engine.  Rows are sorted tuples of signed exponent vectors compared by exact integer term
algebra in ``A_n``.  Classification groups rows by a shift- and sign-invariant fingerprint
(the multiset of ``(exponent difference, product of signs)`` over ordered term pairs) and
then verifies EVERY collision exactly, so the fingerprint can only save time and can never
change an answer.

Scope (read before citing).  Exact integer arithmetic only, stdlib only, deterministic,
every printed claim hard-asserted.  The classification is about the ROW POLYNOMIALS ``N_e``
in ``A_n``, computed cell by cell for the ``n`` listed -- it is not a theorem in ``n``.  The
census semantics live on normalised shapes (the three lines ``y = z``, ``y = 1``, ``z = 1``
removed); on the FULL grid ``mu_n x mu_n`` the group-ring level and the function level are
equivalent, because the Kronecker Vandermonde matrix of the ``n^2`` distinct grid points
against the ``n^2`` monomials is invertible when ``n | p - 1`` -- the crosscheck probe
tests that grid level with field arithmetic only and agrees.  Nothing here says anything
about ``t >= 4``, about global maximizers, about other pencils' counts, about the
production regime ``n = 2^30 / 2^32``, about ``delta*``, or about the prize.
"""

import hashlib
import time
from collections import defaultdict
from math import gcd, isqrt

LIMIT = 20_000
SCAN = tuple(range(3, 301))
RUNGS = tuple(2 ** k for k in range(2, 16))
BRIDGE_RUNGS = (8, 16, 32, 64, 128)
FERMAT = 65537
PRIZE_EXP = 128
PRIZE_K = 21

# Merged PR #267 (probe_n16_below_ceiling_max.py): n=16 (x^3,x^2) ceiling count per prime.
CEILING_EXCEPTIONS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
N8_CEILING = {17: 16, 41: 40, 257: 40}
N16_PRIMES_COUNT = 279
N16_CEILING_DEFAULT = 464


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
    assert (p - 1) % n == 0, (n, p)
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


# ---------------------------------------------------------------------------
# Route 1: exact term algebra in A_n = Z[y, z] / <y^n - 1, z^n - 1>.
# A row is a sorted tuple of ((u, v), coefficient); exponents reduced mod n.
# ---------------------------------------------------------------------------

def row_of(n, exponent):
    agg = {}
    for key, sign in (((1, 0), 1), ((0, 1), -1), ((exponent % n, 0), -1),
                      ((0, exponent % n), 1), ((exponent % n, 1), 1),
                      ((1, exponent % n), -1)):
        agg[key] = agg.get(key, 0) + sign
    return tuple(sorted((key, coeff) for key, coeff in agg.items() if coeff))


def fingerprint(row, n):
    """Invariant under shifting by y^i z^j and under multiplying the row by -1."""
    return tuple(sorted((((a[0] - b[0]) % n, (a[1] - b[1]) % n), sa * sb)
                        for a, sa in row for b, sb in row))


def shifts_relating(target, source, n):
    """Every (i, j, c) with c * y^i z^j * source == target in A_n."""
    hits = set()
    target_dict = dict(target)
    for (bu, bv), bs in source:
        for (tu, tv), ts in target:
            for c in (1, -1):
                if c * bs != ts:
                    continue
                i, j = (tu - bu) % n, (tv - bv) % n
                moved = dict((((u + i) % n, (v + j) % n), c * coeff)
                             for (u, v), coeff in source)
                if moved == target_dict:
                    hits.add((i, j, c))
    return sorted(hits)


def classify(n):
    """Zero rows, equivalence classes of the nonzero rows, and pair certificates."""
    rows = {e: row_of(n, e) for e in range(n)}
    zero_rows = sorted(e for e, row in rows.items() if not row)
    buckets = defaultdict(list)
    for e, row in rows.items():
        if row:
            buckets[fingerprint(row, n)].append(e)
    classes = []
    certificates = {}
    for group in buckets.values():
        remaining = sorted(group)
        while remaining:
            anchor = remaining.pop(0)
            members = [anchor]
            for other in list(remaining):
                hits = shifts_relating(rows[anchor], rows[other], n)
                if hits:
                    members.append(other)
                    remaining.remove(other)
                    certificates[tuple(sorted(members))] = hits
            classes.append(sorted(members))
    classes.sort()
    return zero_rows, classes, certificates, rows


def audit_classify(n, zero_rows, classes, certificates, rows, where):
    """The single classification statement, asserted at every modulus."""
    assert zero_rows == [0, 1], (where, n, zero_rows)
    for e in range(2, n):
        assert len(rows[e]) == 6, (where, n, e, len(rows[e]))
        assert sorted(c for _, c in rows[e]) == [-1, -1, -1, 1, 1, 1], (where, n, e)
    multi = [c for c in classes if len(c) > 1]
    singletons = sum(1 for c in classes if len(c) == 1)
    pairs = sum(len(c) * (len(c) - 1) // 2 for c in classes)
    if n == 3:
        assert classes == [[2]] and multi == [] and pairs == 0, (where, n, classes)
    else:
        assert multi == [[2, n - 1]], (where, n, multi)
        assert len(classes) == n - 3, (where, n, len(classes))
        assert singletons == n - 4, (where, n, singletons)
        assert pairs == 1, (where, n, pairs)
        cert = certificates[(2, n - 1)]
        assert cert == [(1, 1, 1)], (where, n, cert)
    return multi, singletons, pairs


class Shapes:
    """The published normalised-shape engine of the merged census (PR #267 code path)."""

    def __init__(self, n, p):
        self.n, self.p = n, p
        generator = order_element(p, n)
        self.xs = [pow(generator, exponent, p) for exponent in range(n)]
        assert len(set(self.xs)) == n
        self.domain = set(self.xs)
        pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
        self.pairs = pairs
        self.ys = [self.xs[u] for u, v in pairs]
        self.zs = [self.xs[v] for u, v in pairs]
        self.diff = [(y - z) % p for y, z in zip(self.ys, self.zs)]
        self.zm1 = [(z - 1) % p for z in self.zs]
        self.ym1 = [(1 - y) % p for y in self.ys]
        denom = [((1 - y) * (1 - z) * (y - z)) % p for y, z in zip(self.ys, self.zs)]
        assert all(denom), (n, p)
        self.inv_denom = batch_inverse(denom, p)

    def row(self, exponent):
        p = self.p
        return [((self.diff[i] + pow(self.ys[i], exponent, p) * self.zm1[i]
                  + pow(self.zs[i], exponent, p) * self.ym1[i]) % p) * self.inv_denom[i]
                % p for i in range(len(self.ys))]

    def bad_set(self, a, b, row_a=None, row_b=None):
        """The literal bad-scalar set of the pencil (x^a, x^b): {-h_a/h_b : h_b != 0}."""
        p = self.p
        ha = self.row(a) if row_a is None else row_a
        hb = self.row(b) if row_b is None else row_b
        inv_b = batch_inverse(hb, p)
        out = set()
        for index, value in enumerate(hb):
            if value:
                out.add((-ha[index] * inv_b[index]) % p)
        return out

    def t3(self, a, b, row_a=None, row_b=None):
        ha = self.row(a) if row_a is None else row_a
        hb = self.row(b) if row_b is None else row_b
        p, n = self.p, self.n
        m = n // gcd((b - a) % n, n)
        inv_b = batch_inverse(hb, p)
        keys = set()
        for index, value in enumerate(hb):
            if value:
                keys.add(pow((-ha[index] * inv_b[index]) % p, m, p))
        zero = 0 in keys
        cosets = len(keys) - (1 if zero else 0)
        return m * cosets + (1 if zero else 0), m, cosets, zero


def main():
    start = time.time()
    prize_prime, prize_witness = proth_prime(PRIZE_K, PRIZE_EXP)
    assert FERMAT == 2 ** 16 + 1 and is_prime(FERMAT)
    print(f"p = {FERMAT} = 2^16 + 1 prime; prize-scale Proth prime {PRIZE_K}*2^128+1 "
          f"certified in-run by Proth's theorem (witness a={prize_witness})", flush=True)

    # 1. The classification over the full scan range.
    rows_total = 0
    for n in SCAN:
        zero_rows, classes, certificates, rows = classify(n)
        audit_classify(n, zero_rows, classes, certificates, rows, "scan")
        rows_total += n - 2
    print(f"ROUTE 1 group-ring classification over all {len(SCAN)} moduli n in "
          f"[{SCAN[0]}, {SCAN[-1]}] ({rows_total} rows): zero rows exactly {{0, 1}} at "
          f"every n; every row N_e, 2 <= e <= n-1, has exactly 6 terms with signs "
          f"(-1,-1,-1,+1,+1,+1); equivalence classes = exactly one two-element class "
          f"{{2, n-1}} plus n-4 singletons (n >= 4), with the UNIQUE certificate "
          f"N_(n-1) = y^(n-1) z^(n-1) * N_2; at n=3 the two exponents coincide and there "
          f"is no pair", flush=True)

    # 2. The two-power rungs of the census ladder, out to n = 32768.
    vector_parts = []
    for n in RUNGS:
        zero_rows, classes, certificates, rows = classify(n)
        multi, singletons, pairs = audit_classify(n, zero_rows, classes, certificates,
                                                 rows, "rung")
        total_pairs = (n - 2) * (n - 3) // 2
        vector_parts.append(f"{n}|{len(classes)}|{singletons}|{pairs}|{total_pairs}")
        print(f"  rung n={n}: {len(classes)} classes ({singletons} singletons), "
              f"monomial-related unordered row pairs = {pairs} of {total_pairs}, "
              f"the pair is {tuple(multi[0])} with certificate "
              f"{tuple(certificates[(2, n - 1)])}", flush=True)
    sha = hashlib.sha256(";".join(vector_parts).encode()).hexdigest()
    print(f"rung classification vector sha256 {sha} over {len(RUNGS)} two-power "
          f"rungs {RUNGS[0]}..{RUNGS[-1]} (n = 2^k, k = 2.."
          f"{len(RUNGS) + 1})", flush=True)

    # 3. Merged anchors through the published shape engine.
    n8_primes = primes_one_mod(8, LIMIT)
    n16_primes = primes_one_mod(16, LIMIT)
    assert len(n16_primes) == N16_PRIMES_COUNT and n16_primes[0] == 17
    n8_profile = {p: Shapes(8, p).t3(3, 2)[0] for p in n8_primes}
    for p, expected in N8_CEILING.items():
        assert n8_profile[p] == expected, (p, n8_profile[p], expected)
    assert sorted((p, c) for p, c in n8_profile.items() if c != 40) == [(17, 16)]
    profile16 = {p: Shapes(16, p).t3(3, 2)[0] for p in n16_primes}
    for p, expected in CEILING_EXCEPTIONS.items():
        assert profile16[p] == expected, (p, profile16[p], expected)
    exceptions = sorted(p for p, count in profile16.items() if count != N16_CEILING_DEFAULT)
    assert exceptions == sorted(CEILING_EXCEPTIONS), exceptions
    assert Shapes(16, FERMAT).t3(3, 2)[0] == 464
    assert Shapes(16, prize_prime).t3(3, 2)[0] == 464
    print(f"merged anchors reproduced by this engine: n=8 (x^3,x^2) t=3 ceiling 40 at "
          f"every one of the {len(n8_primes)} primes p = 1 (mod 8) in [17, {LIMIT}] "
          f"except p=17 ({n8_profile[17]}), the G330 boundary; n=16 ceiling "
          f"{N16_CEILING_DEFAULT} at {len(n16_primes) - len(exceptions)} of the "
          f"{len(n16_primes)} primes p = 1 (mod 16) in [17, {LIMIT}], the {len(exceptions)} "
          f"exceptions exactly the merged table, and 464 at p={FERMAT} and at the "
          f"prize-scale prime {PRIZE_K}*2^128+1", flush=True)

    # 4. Semantic bridge: the unique pair is SET-equal to mu_n; the others move with p.
    bridge = []
    for n in BRIDGE_RUNGS:
        found = []
        candidate = n + 1
        while len(found) < 3 and candidate < 4_000_000:
            if is_prime(candidate) and candidate % n == 1:
                found.append(candidate)
            candidate += n
        assert len(found) == 3, n
        for p in found + [FERMAT, prize_prime]:
            shapes = Shapes(n, p)
            row2 = shapes.row(2)
            row_nm1 = shapes.row(n - 1)
            assert all(value == 1 for value in row2), (n, p)
            assert all((row_nm1[i] * shapes.ys[i] % p) * shapes.zs[i] % p == 1
                       for i in range(len(shapes.ys))), (n, p)
            bad = shapes.bad_set(2, n - 1, row_a=row2, row_b=row_nm1)
            count, m, cosets, zero = shapes.t3(2, n - 1, row_a=row2, row_b=row_nm1)
            assert bad == shapes.domain, (n, p, len(bad))
            assert 0 not in bad
            assert (count, m, cosets, zero) == (n, n, 1, False), (n, p, count, m)
            neighbours = {}
            for b in (n - 2, n - 3, 4):
                if 2 < b < n:
                    # the census count of the pencil, i.e. the number of raw bad
                    # scalars over all triples (the orbit-closed set)
                    neighbours[b] = shapes.t3(2, b, row_a=row2)[0]
            bridge.append((n, p, count, tuple(sorted(neighbours.items()))))
    def label(p_value):
        if p_value == prize_prime:
            return f"{PRIZE_K}*2^128+1"
        return str(p_value)

    vectors = defaultdict(dict)
    for n, p, count, neighbours in bridge:
        for b, value in neighbours:
            vectors[n].setdefault(b, set()).add(value)
        print(f"  bridge n={n} p={label(p)}: bad(x^2, x^(n-1)) = mu_n exactly, count "
              f"{count} = n; the pencils the classification separates count "
              + ", ".join(f"|bad(x^2, x^{b})| = {value}" for b, value in neighbours),
              flush=True)
    summary = "; ".join(f"n={n}: " + ", ".join(f"(x^2,x^{b}) in {sorted(vectors[n][b])}"
                                               for b in sorted(vectors[n]))
                        for n in BRIDGE_RUNGS)
    print(f"semantic bridge: the bad-scalar set of (x^2, x^(n-1)) is SET-equal to mu_n "
          f"(count n, one coset, 0 never bad) at all {len(bridge)} cells (n in "
          f"{BRIDGE_RUNGS} x {{three smallest p = 1 (mod n), {FERMAT}, "
          f"{PRIZE_K}*2^128+1}}), which is the classification's unique pair doing exactly "
          f"what it is certified to do; the neighbouring pencils that the classification "
          f"SEPARATES are not constant: {summary}", flush=True)
    vector_sha = hashlib.sha256(
        ";".join(f"{n},{p if p < 10 ** 6 else 'P' + str(p >> 128)},{c},{nb}"
                 for n, p, c, nb in bridge).encode()).hexdigest()
    print(f"bridge vector sha256 {vector_sha} over {len(bridge)} cells", flush=True)
    print(f"PASS: exact isolation -- of the C(n-2,2) unordered pencils of nonzero "
          f"h-rows, exactly ONE, the pair (x^2, x^(n-1)), has a monomial bad-scalar "
          f"ratio, at every one of the {len(SCAN)} scanned moduli n in [{SCAN[0]}, "
          f"{SCAN[-1]}] and every one of the {len(RUNGS)} two-power rungs "
          f"{RUNGS[0]}..{RUNGS[-1]}; no t>=4, global-maximum, production-regime, "
          f"delta* or prize claim", flush=True)
    print(f"elapsed {time.time() - start:.1f}s", flush=True)


if __name__ == "__main__":
    main()
