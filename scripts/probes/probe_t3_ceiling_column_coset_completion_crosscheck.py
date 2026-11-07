#!/usr/bin/env python3
"""Independent routes to the coset-completion result of the column ``b = n - 1``.

The companion ``probe_t3_ceiling_column_coset_completion.py`` computes the ceiling bad set from
the closed form ``h_e(1, y, z)`` on the ``C(n-1,2)`` normalised shapes and identifies cosets of
the order-``m`` subgroup of ``mu_n`` by the key ``pow(gamma, m, p)``.  This script reaches the
same integers by routes that share no code and no algebraic path with it.

* ROUTE A (``|B|`` directly) -- at ``n = 8, 16, 32, 64`` every ``C(n,3)`` triple ``T`` of
  ``mu_n`` is enumerated (no shape normalisation, so the shape reduction itself is being
  checked).  ``gamma`` is bad iff the points ``(x, x^a + gamma*x^b)``, ``x in T``, are collinear,
  i.e. ``D_a(T) + gamma*D_b(T) = 0`` for the ``3x3`` determinant
  ``D_e(T) = r2*r3^e - r3*r2^e - r1*r3^e + r3*r1^e + r1*r2^e - r2*r1^e``, evaluated term by
  term by Sarrus.  The bad set is then the literal set of ``-D_a/D_b``, and its cardinality is
  the count -- no subgroup arithmetic is involved at all.
* ROUTE B (cosets by discrete logarithm) -- a full logarithm table over a primitive root is
  built once per prime; two scalars are in one coset of the order-``m`` subgroup iff their
  logarithms are congruent modulo ``(p-1)/m``.  The companion's ``pow(gamma, m, p)`` keying is
  never used at ``65537``.
* ROUTE C (orbit closure) -- the bad set is rebuilt as the literal union of multiplicative
  orbits ``gamma * mu_m`` and its size compared with ``m*cosets + epsilon``; membership in the
  set is checked element by element, and a complete cell is asserted to close to EXACTLY ``F_p``
  (``0`` bad) or ``F_p \\ {0}`` (``0`` not bad) as a set identity, not as a count.
* At the higher rungs ``n = 128, 256, 512`` all-triples enumeration is ``C(n,3) >= 341120`` per
  cell and out of reach, so ROUTE A runs on normalised shapes there with the same Sarrus
  determinants, and the coset count uses ROUTE B.  Over the prize-scale Proth prime
  ``21*2^128+1`` a logarithm table is impossible, so the subgroup key ``pow(gamma, m, p)`` is
  used there -- that single cell of the method is the companion's, and it is stated as such.

Everything is exact integer arithmetic, stdlib only, deterministic; every printed claim is
hard-asserted and the script exits ``0`` only on ``PASS``.

Scope mirrors the companion: the listed rungs, the primes named below, one column of the
monomial-pencil ``t = 3`` census on ``mu_n``.  Nothing here is a theorem in ``n`` or ``p``, a
``t >= 4`` statement, a global-maximum statement, a production-regime statement, or a ``delta*``
or prize claim.
"""

import hashlib
from math import gcd, isqrt

FERMAT = 65537
PRIZE = 21 * (2 ** 128) + 1
PRIZE_LABEL = "21*2^128+1"
LIMIT = 20_000
TRIPLE_RUNGS = (8, 16, 32, 64)
SHAPE_RUNGS = (128, 256, 512)
FERMAT_RUNGS = TRIPLE_RUNGS + SHAPE_RUNGS

PUBLISHED_DIGESTS = {
    (8, FERMAT): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, FERMAT): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, FERMAT): "3cce569863d7fdac3b3c966abcb1c1344bbe0419121e58bdfadb3f0bea11c961",
    (64, FERMAT): "69f3e4c5416969ea428cf7fb0e96abd83ba6f6fc3ea11a9932313dfe6d5dfa1c",
    (128, FERMAT): "5630704e234513e22d52b9d06f0bb46c3905869e5d675ec99f2194f2be3a8211",
    (256, FERMAT): "238075666216e34ee9b077a22933f0063e4b64c7e35a4a88440c4ba8e5af4f81",
    (512, FERMAT): "db7cd7e9bc2c5026039833dd18814db852a0463399564467d7f2e526bf5d1222",
    (64, PRIZE): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
}
PUBLISHED_SATURATED = {8: 0, 16: 0, 32: 0, 64: 0, 128: 1, 256: 173, 512: 442}
PUBLISHED_ZERO = {8: 4, 128: 76, 256: 188, 512: 444}
PUBLISHED_COLUMNS = {64: ((2,), 1, 30784, 1127669), 128: ((2,), 1, 65537, 6885189)}
N8_DEFAULT, N8_EXCEPTIONS = 40, {17: 16}
N16_DEFAULT, N16_EXCEPTIONS = 464, {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
CLAIM = {256: (lambda a: a % 8 != 7, {0, 1, 2, 3}, "a mod 8 != 7"),
         512: (lambda a: a % 64 != 63, {0, 1, 2}, "a mod 64 != 63")}


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


def prime_factors(value):
    out, divisor = set(), 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            out.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        out.add(value)
    return sorted(out)


def primitive_root(p):
    for candidate in range(2, p):
        if all(pow(candidate, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return candidate
    raise AssertionError(p)


def order_element(p, n):
    assert (p - 1) % n == 0, (p, n)
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            return generator
    raise AssertionError((p, n))


class LogTable:
    """Discrete logarithms; the coset test is a congruence on logarithms."""

    def __init__(self, p):
        self.p = p
        root = primitive_root(p)
        table = [0] * p
        value = 1
        for exponent in range(p - 1):
            assert table[value] == 0, (p, value)
            table[value] = exponent
            value = value * root % p
        assert value == 1
        self.table = table

    def cosets(self, scalars, m):
        assert (self.p - 1) % m == 0
        modulus = (self.p - 1) // m
        classes = {self.table[value] % modulus for value in scalars if value}
        return len(classes), (1 if any(not value for value in scalars) else 0)


def invert_all(values, p):
    """Prefix/suffix product tree: one modular exponentiation for a whole list of inverses."""
    count = len(values)
    prefix, suffix = [1] * (count + 1), [1] * (count + 1)
    for index in range(count):
        prefix[index + 1] = prefix[index] * (values[index] or 1) % p
    for index in range(count - 1, -1, -1):
        suffix[index] = suffix[index + 1] * (values[index] or 1) % p
    running = pow(prefix[count], p - 2, p)
    out = [0] * count
    for index in range(count):
        if values[index]:
            out[index] = running * prefix[index] % p * suffix[index + 1] % p
            assert values[index] * out[index] % p == 1, (p, index)
    return out


def determinant(r1, r2, r3, exponent, p):
    """``D_e(T)`` for ``T = {r1, r2, r3}``, the 3x3 collinearity determinant, by Sarrus."""
    e1, e2, e3 = pow(r1, exponent, p), pow(r2, exponent, p), pow(r3, exponent, p)
    return (r2 * e3 - r3 * e2 - r1 * e3 + r3 * e1 + r1 * e2 - r2 * e1) % p


class Detector:
    def __init__(self, n, p, want_logs=True):
        self.n, self.p = n, p
        self.points = None
        self.cached_b = None
        self.generator = order_element(p, n)
        self.xs = [pow(self.generator, e, p) for e in range(n)]
        assert len(set(self.xs)) == n
        self.logs = LogTable(p) if want_logs and p < 200_000 else None

    def triples(self, use_all):
        xs = self.xs
        if use_all:
            for i in range(self.n):
                for j in range(i + 1, self.n):
                    for k in range(j + 1, self.n):
                        yield (xs[i], xs[j], xs[k])
        else:
            for j in range(1, self.n):
                for k in range(j + 1, self.n):
                    yield (xs[0], xs[j], xs[k])

    def bad_set(self, a, b, use_all):
        if not hasattr(self, "points") or self.cached_b != b:
            self.points = list(self.triples(use_all))
            self.cached_b = b
            self.db = [determinant(r1, r2, r3, b, self.p) for (r1, r2, r3) in self.points]
            self.inv_db = invert_all(self.db, self.p)
        da = [determinant(r1, r2, r3, a, self.p) for (r1, r2, r3) in self.points]
        return {(-da[i] * self.inv_db[i]) % self.p
                for i in range(len(self.points)) if self.db[i]}

    def m_of(self, a, b):
        return self.n // gcd((b - a) % self.n, self.n)


def mu_subgroup(p, order):
    """The order-`order` subgroup of F_p^*, as an explicit set."""
    if order == 1:
        return {1}
    generator = order_element(p, order)
    return {pow(generator, e, p) for e in range(order)}


def describe(values):
    return "{" + ", ".join(str(v) for v in sorted(values)) + "}"


def main():
    print("crosscheck: Sarrus determinants, discrete-log cosets, orbit-closure sets", flush=True)
    assert is_prime(FERMAT) and 21 % 2 == 1 and 21 < 2 ** 128
    assert [w for w in range(2, 64) if pow(w, (PRIZE - 1) // 2, PRIZE) == PRIZE - 1]
    print(f"fields: {FERMAT} prime; {PRIZE_LABEL} prime by Proth (k=21 < 2^128); primitive "
          f"root {primitive_root(FERMAT)} and logarithm table of length {FERMAT} built once",
          flush=True)

    for n, default, exceptions, modulus in ((8, N8_DEFAULT, N8_EXCEPTIONS, 8),
                                            (16, N16_DEFAULT, N16_EXCEPTIONS, 16)):
        primes = primes_one_mod(modulus, LIMIT)
        ordinary, listed = 0, {}
        for p in primes:
            det = Detector(n, p)
            count = len(det.bad_set(3, 2, True))
            if p in exceptions:
                assert count == exceptions[p], (n, p, count, exceptions[p])
                listed[p] = count
            else:
                assert count == default, (n, p, count)
                ordinary += 1
        assert listed == exceptions
        print(f"merged anchor n={n} by ROUTE A over all C({n},3) triples: ceiling {default} at "
              f"{ordinary} of {len(primes)} primes p = 1 (mod {modulus}) in [17, {LIMIT}], the "
              f"other {len(listed)} exactly the published exception table", flush=True)

    results = {}
    for n in FERMAT_RUNGS:
        use_all = n in TRIPLE_RUNGS
        det = Detector(n, FERMAT)
        cells, counts = {}, []
        m = None
        for a in range(n):
            bad = det.bad_set(a, n - 1, use_all)
            m = det.m_of(a, n - 1)
            if use_all:
                count, epsilon = len(bad), (1 if 0 in bad else 0)
                cosets, log_eps = det.logs.cosets(bad, m)
                assert log_eps == epsilon and cosets * m + epsilon == count, (n, a)
                if n <= 32:  # the closure is |bad| * m pairs; affordable at these rungs
                    assert bad == {g * z % FERMAT for g in bad for z in
                                   mu_subgroup(FERMAT, m)} | ({0} if epsilon else set()), (n, a)
            else:
                cosets, epsilon = det.logs.cosets(bad, m)
                count = m * cosets + epsilon
            cells[a] = (count, m, cosets, epsilon)
            counts.append(count)
            assert m == n // gcd((n - 1 - a) % n, n)
        digest = hashlib.sha256(",".join(str(c) for c in counts).encode()).hexdigest()
        assert digest == PUBLISHED_DIGESTS[(n, FERMAT)], (n, digest)
        saturated = sorted(a for a in range(n) if counts[a] == FERMAT)
        assert len(saturated) == PUBLISHED_SATURATED[n], (n, len(saturated))
        zero = sorted(a for a in range(n) if cells[a][3])
        if n in PUBLISHED_ZERO:
            assert len(zero) == PUBLISHED_ZERO[n], (n, len(zero))
        if n in PUBLISHED_COLUMNS:
            exact_n = tuple(sorted(a for a in range(n) if counts[a] == n))
            assert (exact_n, min(counts), max(counts), sum(counts)) == PUBLISHED_COLUMNS[n], n
        complete = sorted(a for a in range(n) if cells[a][2] == (FERMAT - 1) // cells[a][1])
        assert saturated == sorted(set(complete) & set(zero)), n
        for a in complete:
            assert counts[a] in (FERMAT, FERMAT - 1)
        for a in range(n):
            if a not in set(complete):
                assert counts[a] not in (FERMAT, FERMAT - 1), (n, a, counts[a])
        results[n] = (cells, counts, complete, zero, saturated, det)
        print(f"n={n} at {FERMAT} by ROUTE {'A (all C(n,3) triples, |B| directly)' if use_all else 'A on shapes + B (discrete log)'}: "
              f"digest {digest[:16]} pinned; complete {len(complete)}; saturated {len(saturated)}"
              f" = complete ^ zero ({len(complete)} ^ {len(zero)}); zero {len(zero)}", flush=True)
        if n in CLAIM:
            predicate, drop, law = CLAIM[n]
            claimed = sorted(a for a in range(n) if predicate(a) and a not in drop)
            assert claimed == complete, (n, describe(set(claimed) ^ set(complete)))
            print(f"  COMPLETENESS LAW n={n} reproduced here: complete = {{a : {law}}} \\ "
                  f"{describe(drop)}; exceptions = {describe(set(range(n)) - set(claimed))}",
                  flush=True)

    closed, total_elements = 0, 0
    for n in (256, 512):
        cells, counts, complete, zero, saturated, det = results[n]
        sample = complete[:4] + complete[len(complete) // 2:len(complete) // 2 + 2] \
            + complete[-2:] + [2, 0, 1] + [a for a in range(n) if a not in set(complete)][:3]
        for a in sorted(set(sample)):
            count, m, cosets, epsilon = cells[a]
            bad = det.bad_set(a, n - 1, False)
            sub = mu_subgroup(FERMAT, m)
            assert len(sub) == m
            orbit = {g * z % FERMAT for g in bad if g for z in sub}
            if epsilon:
                orbit.add(0)
            total_elements += len(orbit)
            assert len(orbit) == count == m * cosets + epsilon, (n, a, len(orbit), count)
            generator = order_element(FERMAT, m) if m > 1 else 1
            for element in orbit:
                if element:
                    assert element * generator % FERMAT in orbit, (n, a)
            if cosets == (FERMAT - 1) // m:
                assert orbit == (set(range(FERMAT)) if epsilon
                                 else set(range(1, FERMAT))), (n, a)
                closed += 1
    print(f"ROUTE C: {closed} complete cells at n = 256 and n = 512 rebuilt as literal unions "
          f"of multiplicative orbits of the order-m subgroup ({total_elements} set elements "
          f"constructed) -- each closes to EXACTLY F_p or F_p \\ {{0}}, mu_m-invariance checked "
          f"element by element, and the orbit size equals m*cosets + epsilon", flush=True)

    det = Detector(64, PRIZE, want_logs=False)
    counts, complete = [], []
    for a in range(64):
        bad = det.bad_set(a, 63, False)
        m = det.m_of(a, 63)
        keys = {pow(g, m, PRIZE) for g in bad}
        epsilon = 1 if 0 in keys else 0
        cosets = len(keys) - epsilon
        counts.append(m * cosets + epsilon)
        if cosets == (PRIZE - 1) // m:
            complete.append(a)
    digest = hashlib.sha256(",".join(str(c) for c in counts).encode()).hexdigest()
    assert digest == PUBLISHED_DIGESTS[(64, PRIZE)], digest
    assert complete == []
    required_min = min((PRIZE - 1) // (64 // gcd((63 - a) % 64, 64)) for a in range(64))
    print(f"prize prime n=64 by the Sarrus route: digest {digest[:16]} pinned; 0 of 64 cells "
          f"complete; smallest group bound (p-1)/m = {required_min} exceeds both the "
          f"{63 * 62 // 2} shapes and the {64 * 63 * 62 // 6} triples, so completeness there is "
          f"excluded by counting (the subgroup key pow(gamma, m, p) is the only step shared "
          f"with the companion, because logarithm tables modulo {PRIZE_LABEL} are impossible)",
          flush=True)

    print(f"PASS: independent routes agree with the companion on all {sum(FERMAT_RUNGS)} cells "
          f"of the column b = n-1 over {FERMAT} -- every pinned column digest, the merged 40 "
          f"and 464 ceiling tables, the completeness laws {{a : a mod 8 != 7}} \\ {{0,1,2,3}} at "
          f"n = 256 and {{a : a mod 64 != 63}} \\ {{0,1,2}} at n = 512, the saturation tallies "
          f"173 and 442 as complete ^ zero, and 0 complete cells over {PRIZE_LABEL} at n = 64 "
          f"-- by |B| read off all C(n,3) triples with Sarrus 3x3 determinants at n <= 64, by "
          f"discrete-log coset classes instead of exponent keys, and by orbit-closure set "
          f"identities; no theorem in n or p, no t>=4, no global maximum, no production "
          f"regime, no delta* or prize claim", flush=True)


if __name__ == "__main__":
    main()
