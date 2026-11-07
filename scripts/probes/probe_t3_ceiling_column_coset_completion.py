#!/usr/bin/env python3
"""Coset completion in the column ``b = n - 1`` of the ``t = 3`` ceiling census at ``65537``.

Object.  Fix a prime ``p = 1 (mod n)``, an element ``g`` of exact order ``n``, the domain
``mu_n = {g^0, ..., g^(n-1)}`` and the dimension-two code of affine words ``c0 + c1*x``.  For the
pencil ``(u0, u1) = (x^a, x^b)`` the ceiling (``t = 3``) bad scalars are the ``gamma`` for which
``x^a + gamma*x^b`` agrees with an affine word on some triple ``T`` while ``(x^a, x^b)`` is not
jointly affine on ``T``.  With the collinearity determinants ``D_e(T)`` that is
``gamma = -D_a(T)/D_b(T)``, dilating ``T`` sends ``gamma`` to ``gamma * g``, and the pencil is
invariant under ``gamma -> gamma * zeta`` for ``zeta`` in the order-``m`` subgroup with
``m = m(a) = n / gcd((b-a) mod n, n)``, so the bad set is a union of cosets of that subgroup:

    count(a) = m(a) * cosets(a) + epsilon(a),   cosets(a) <= (p-1)/m(a),   cosets <= C(n-1,2),

with ``epsilon(a) = 1`` iff ``0`` is bad, and ``C(n-1,2)`` the number of normalised shapes.  A
cell is called **complete** when ``cosets(a)`` reaches the group bound ``(p-1)/m(a)``, i.e. when
the bad set is as large as the field allows: ``count = p`` if ``0`` is bad, ``count = p - 1``
if it is not.

What this probe adds.  The campaign's open PR #351 companion prints this column at ``n = 64``
and ``n = 128`` over ``65537``, and the staged high-rung column probe prints it at ``n = 8``
through ``n = 512``; both report that the saturation sets (``count = p``) at ``n = 256``
(173 pencils) and ``n = 512`` (442 pencils) have NO residue-class description.  This probe
supplies the missing factor:

* the decomposition ``count = m*cosets + epsilon`` holds at all 1016 cells over ``65537`` at
  ``n = 8, 16, 32, 64, 128, 256, 512``, with ``m`` recomputed from an independent gcd;
* completeness is empty at ``n <= 64``, one cell at ``n = 128``, and then generic: exactly
  ``{a : a != 7 (mod 8)} \\ {0, 1, 2, 3}`` at ``n = 256`` (220 of 256 cells) and exactly
  ``{a : a != 63 (mod 64)} \\ {0, 1, 2}`` at ``n = 512`` (501 of 512 cells);
* the two undescribable saturation sets are exactly (complete set) intersected with
  (zero-membership set): ``173`` at ``n = 256`` out of ``220`` complete and ``188`` zero-carrying
  cells, and ``442`` at ``n = 512`` out of ``501`` and ``444`` -- the published tallies;
* the ``65537`` exceptions are NOT excluded by counting (``(p-1)/m < C(n-1,2)`` there with room
  to spare), while over the prize-scale Proth prime ``21*2^128+1`` NO cell is complete and the
  reason IS counting: ``(p-1)/m >= (p-1)/n > C(n-1,2)``, so the ``65537`` saturation is a
  small-prime cap artifact -- the discipline ``Research/ProximityPrize/AGENTS.md`` (G84/SYZ53)
  makes mandatory.

Reproduced first, before any new claim: the merged ``(x^3, x^2)`` ceiling tables of
``scripts/probes/probe_order16_weight13_spectrum.py`` (PR #264) and
``scripts/probes/probe_n16_below_ceiling_max.py`` (PR #267) -- ``40`` at every prime
``p = 1 (mod 8)`` in ``[17, 20000]`` except ``17: 16``, and ``464`` at ``245`` of the ``279``
primes ``p = 1 (mod 16)`` with the other ``34`` exactly the merged exception table -- plus the
published column data being decomposed: the vector sha256 of each of the seven columns, the
quadruples ``n = 64 -> ((2,), 1, 30784, 1127669)`` and ``n = 128 -> ((2,), 1, 65537, 6885189)``,
the saturation tallies ``0, 0, 0, 0, 1, 173, 442``, the zero-membership sizes ``4, 76, 188, 444``
and the three prize-regime column digests.

Scope, read before citing.  Finite fields, the seven listed rungs, the two listed primes, ONE
column of the monomial-pencil census, on ``mu_n``.  The completeness descriptions are computed
facts at the listed cells, not a theorem in ``n`` or ``p``; no mechanism is proved for why an
individual cell is or is not complete; ``t >= 4``, other columns and rows, the global maximum of
any census, the production regime ``n = 2^30 / 2^32``, ``delta*`` and the prize are untouched.
``count <= m*C(n-1,2) + 1`` is a counting bound on this enumeration, not a complexity statement.
"""

import hashlib
from math import gcd, isqrt

LIMIT = 20_000
FERMAT = 65537
PRIZE = 21 * (2 ** 128) + 1
PRIZE_LABEL = "21*2^128+1"
RUNGS = (8, 16, 32, 64, 128, 256, 512)
PRIZE_RUNGS = (64, 128, 256)

PUBLISHED_DIGESTS = {
    (8, FERMAT): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, FERMAT): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, FERMAT): "3cce569863d7fdac3b3c966abcb1c1344bbe0419121e58bdfadb3f0bea11c961",
    (64, FERMAT): "69f3e4c5416969ea428cf7fb0e96abd83ba6f6fc3ea11a9932313dfe6d5dfa1c",
    (128, FERMAT): "5630704e234513e22d52b9d06f0bb46c3905869e5d675ec99f2194f2be3a8211",
    (256, FERMAT): "238075666216e34ee9b077a22933f0063e4b64c7e35a4a88440c4ba8e5af4f81",
    (512, FERMAT): "db7cd7e9bc2c5026039833dd18814db852a0463399564467d7f2e526bf5d1222",
    (64, PRIZE): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
    (128, PRIZE): "baa6b0809122b4350b40d6482ba73974afe41e24b2d5855ccb55a76c13d8a5fb",
    (256, PRIZE): "d1aefd564a8c61afbd68dd21799aa14fea01efba79b8e0cd18542d6b25db213a",
}
PUBLISHED_COLUMNS = {64: ((2,), 1, 30784, 1127669), 128: ((2,), 1, 65537, 6885189)}
PUBLISHED_SATURATED = {8: 0, 16: 0, 32: 0, 64: 0, 128: 1, 256: 173, 512: 442}
PUBLISHED_ZERO = {8: 4, 128: 76, 256: 188, 512: 444}

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

COMPLETENESS_CLAIM = {
    256: ("a mod 8 != 7", lambda a: a % 8 != 7, {0, 1, 2, 3}, "a mod 8 == 7"),
    512: ("a mod 64 != 63", lambda a: a % 64 != 63, {0, 1, 2}, "a mod 64 == 63"),
}


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


def order_element(p, n):
    assert (p - 1) % n == 0, (p, n)
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
    running = pow(prefix[-1], -1, p)
    out = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        value = values[index]
        if value:
            out[index] = running * prefix[index] % p
            running = running * value % p
    return out


class Census:
    """Normalised shapes ``{1, y, z}`` of ``mu_n`` and the ``h``-rows of pencil exponents."""

    def __init__(self, n, p):
        self.n, self.p = n, p
        self.generator = order_element(p, n)
        xs = [pow(self.generator, e, p) for e in range(n)]
        assert len(set(xs)) == n and xs[0] == 1
        pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
        self.shape_count = len(pairs)
        self.ys = [xs[u] for u, v in pairs]
        self.zs = [xs[v] for u, v in pairs]
        self.diff = [(y - z) % p for y, z in zip(self.ys, self.zs)]
        self.zm1 = [(z - 1) % p for z in self.zs]
        self.ym1 = [(1 - y) % p for y in self.ys]
        denom = [self.ym1[i] * self.zm1[i] % p * self.diff[i] % p
                 for i in range(self.shape_count)]
        assert all(denom), "distinct 1, y, z required"
        self.inv_denom = batch_inverse(denom, p)

    def row(self, exponent):
        p, ys, zs = self.p, self.ys, self.zs
        diff, zm1, ym1, inv = self.diff, self.zm1, self.ym1, self.inv_denom
        return [((diff[i] + pow(ys[i], exponent, p) * zm1[i]
                  + pow(zs[i], exponent, p) * ym1[i]) % p) * inv[i] % p
                for i in range(self.shape_count)]

    def cell(self, a, b, row_a, row_b, inv_b):
        """(count, m, cosets, epsilon) for the ceiling event of the pencil (x^a, x^b)."""
        p, n = self.p, self.n
        m = n // gcd((b - a) % n, n)
        keys = {pow((-row_a[i] * inv_b[i]) % p, m, p)
                for i in range(self.shape_count) if row_b[i]}
        epsilon = 1 if 0 in keys else 0
        cosets = len(keys) - epsilon
        count = m * cosets + epsilon
        assert len(keys) <= self.shape_count
        assert count <= m * self.shape_count + 1
        return count, m, cosets, epsilon

    def column(self):
        """Every cell of the column ``b = n-1`` plus the count vector."""
        row_b = self.row(self.n - 1)
        inv_b = batch_inverse(row_b, self.p)
        cells, counts = {}, []
        for a in range(self.n):
            cell = self.cell(a, self.n - 1, self.row(a), row_b, inv_b)
            cells[a] = cell
            counts.append(cell[0])
        return cells, counts

    def ceiling_count(self, a, b):
        row_a, row_b = self.row(a), self.row(b)
        inv_b = batch_inverse(row_b, self.p)
        return self.cell(a, b, row_a, row_b, inv_b)[0]


def digest(counts):
    return hashlib.sha256(",".join(str(c) for c in counts).encode()).hexdigest()


def replay_merged_ceiling():
    for n, default, exceptions, prime_count, modulus in (
            (8, N8_CEILING_DEFAULT, N8_CEILING_EXCEPTIONS, N8_PRIME_COUNT, 8),
            (16, N16_CEILING_DEFAULT, N16_CEILING_EXCEPTIONS, N16_PRIME_COUNT, 16)):
        primes = primes_one_mod(modulus, LIMIT)
        assert len(primes) == prime_count and all(is_prime(p) for p in primes)
        ordinary, listed = 0, {}
        for p in primes:
            count = Census(n, p).ceiling_count(3, 2)
            if p in exceptions:
                assert count == exceptions[p], (n, p, count, exceptions[p])
                listed[p] = count
            else:
                assert count == default, (n, p, count)
                ordinary += 1
        assert listed == exceptions, (n, sorted(listed))
        assert ordinary + len(listed) == prime_count
        print(f"merged anchor n={n}: (x^3,x^2) ceiling {default} at {ordinary} of "
              f"{prime_count} primes p = 1 (mod {modulus}) in [17, {LIMIT}]; the other "
              f"{len(listed)} are exactly the published exception table", flush=True)


def describe(values):
    return "{" + ", ".join(str(v) for v in sorted(values)) + "}"


def main():
    print("t=3 ceiling column b=n-1: coset completion at 65537 and at the prize prime",
          flush=True)
    assert is_prime(FERMAT) and 21 % 2 == 1 and 21 < 2 ** 128
    proth = [w for w in range(2, 64) if pow(w, (PRIZE - 1) // 2, PRIZE) == PRIZE - 1]
    assert proth, PRIZE
    print(f"fields: {FERMAT} = 2^16+1 prime; {PRIZE_LABEL} prime by Proth's theorem "
          f"(k=21 < 2^128, witness {proth[0]}); mu_n generators of exact order n found per "
          f"rung by search with g^(n/2) = -1 certified", flush=True)
    replay_merged_ceiling()

    fermat_data = {}
    for n in RUNGS:
        census = Census(n, FERMAT)
        cells, counts = census.column()
        assert digest(counts) == PUBLISHED_DIGESTS[(n, FERMAT)], n
        exact_n = tuple(sorted(a for a in range(n) if counts[a] == n))
        if n in PUBLISHED_COLUMNS:
            assert (exact_n, min(counts), max(counts), sum(counts)) == PUBLISHED_COLUMNS[n], n
        saturated = sorted(a for a in range(n) if counts[a] == FERMAT)
        assert len(saturated) == PUBLISHED_SATURATED[n], (n, len(saturated))
        zero = sorted(a for a in range(n) if cells[a][3])
        if n in PUBLISHED_ZERO:
            assert len(zero) == PUBLISHED_ZERO[n], (n, len(zero))
        complete, partial = [], []
        for a in range(n):
            count, m, cosets, epsilon = cells[a]
            assert m == n // gcd((n - 1 - a) % n, n), (n, a)
            assert count == m * cosets + epsilon and count % m == epsilon, (n, a)
            required = (FERMAT - 1) // m
            assert cosets <= required
            (complete if cosets == required else partial).append(a)
            if cosets == required:
                assert count in (FERMAT, FERMAT - 1) and count == FERMAT - 1 + epsilon
            else:
                assert count not in (FERMAT, FERMAT - 1), (n, a, count, m, epsilon)
        assert saturated == sorted(set(complete) & set(zero)), n
        surplus = min((FERMAT - 1) // cells[a][1] - cells[a][2] for a in partial) if partial else None
        required_min = min((FERMAT - 1) // cells[a][1] for a in range(n))
        feasible = "possible" if required_min <= census.shape_count else "impossible"
        print(f"column b = {n-1} at p = {FERMAT}: {len(complete)} of {n} cells complete; "
              f"saturation {len(saturated)} = complete ^ zero "
              f"({len(complete)} ^ {len(zero)}); count = p-1 at "
              f"{sum(1 for a in complete if not cells[a][3])} complete cells; smallest coset "
              f"deficit among the {len(partial)} incomplete cells = {surplus}; completeness is "
              f"{feasible} by counting here since min (p-1)/m = {required_min} vs "
              f"C({n-1},2) = {census.shape_count}", flush=True)
        fermat_data[n] = (cells, counts, complete, partial, zero, saturated)

    for n in (256, 512):
        cells, counts, complete, partial, zero, saturated = fermat_data[n]
        law, predicate, drop, exception_law = COMPLETENESS_CLAIM[n]
        claimed = sorted(a for a in range(n) if predicate(a) and a not in drop)
        assert claimed == complete, (n, len(claimed), len(complete),
                                     describe(set(claimed) ^ set(complete)))
        assert sorted(partial) == sorted(set(range(n)) - set(claimed)), n
        non_degenerate = [a for a in partial if a not in drop]
        assert non_degenerate == [a for a in range(n) if not predicate(a)], (
            n, describe(set(non_degenerate) ^ {a for a in range(n) if not predicate(a)}))
        print(f"COMPLETENESS LAW n={n}: complete = {{a : {law}}} \\ {describe(drop)}, exact on "
              f"all {n} cells; the incomplete cells are {describe(drop)} plus "
              f"{{a : {exception_law}}} ({len(non_degenerate)} cells), so the exception set is "
              f"itself a congruence class plus three or four degenerate pencils", flush=True)
        deficits = sorted({(cells[a][1], (FERMAT - 1) // cells[a][1] - cells[a][2])
                           for a in partial if a not in drop})
        print(f"  the non-degenerate exceptions all sit at small m: "
              f"m values {sorted({cells[a][1] for a in partial if a not in drop})}, deficits "
              f"{min(d for _, d in deficits)}..{max(d for _, d in deficits)} cosets", flush=True)

    for n in (8, 16, 32, 64, 128):
        complete = fermat_data[n][2]
        print(f"  complete set at n={n}: {describe(complete)}", flush=True)

    prize_data = {}
    for n in PRIZE_RUNGS:
        census = Census(n, PRIZE)
        cells, counts = census.column()
        assert digest(counts) == PUBLISHED_DIGESTS[(n, PRIZE)], n
        complete = [a for a in range(n) if cells[a][2] == (PRIZE - 1) // cells[a][1]]
        assert complete == [], (n, complete)
        required_min = min((PRIZE - 1) // cells[a][1] for a in range(n))
        max_count = max(counts)
        assert required_min > census.shape_count, (n, required_min, census.shape_count)
        slack = min(cells[a][1] * census.shape_count + 1 - cells[a][0] for a in range(n))
        print(f"column b = {n-1} at p = {PRIZE_LABEL}: 0 of {n} cells complete; the group bound "
              f"(p-1)/m is at least {required_min} while only C({n-1},2) = "
              f"{census.shape_count} cosets can be hit, so completeness is excluded by "
              f"counting; shape cap count <= m*C(n-1,2)+1 holds at every cell with slack "
              f"at least {slack}; column max {max_count}", flush=True)
        prize_data[n] = counts

    differing = [n for n in PRIZE_RUNGS if fermat_data[n][1] != prize_data[n]]
    assert differing == list(PRIZE_RUNGS), differing
    print(f"cross-regime: at the rungs computed in both regimes (n = 64, 128, 256) the column "
          f"vectors differ over the two primes; the complete-cell counts are "
          f"{[len(fermat_data[n][2]) for n in PRIZE_RUNGS]} at {FERMAT} against "
          f"[0, 0, 0] at {PRIZE_LABEL}. The {FERMAT} saturation and p-1 plateau are cap "
          f"artifacts of the small quotient group F_p^*/mu_n of order (p-1)/m, not a property "
          f"of the pencils, which are the same objects at both primes", flush=True)
    print(f"PASS: exact coset completion of the column b = n-1 over {FERMAT} at all "
          f"{sum(RUNGS)} cells -- count = m*cosets + epsilon with m = n/gcd(b-a,n) recomputed "
          f"independently, complete cells are exactly those with cosets = (p-1)/m, empty at "
          f"n <= 64, one cell at n = 128, {{a : a mod 8 != 7}} \\ {{0,1,2,3}} at n = 256 (220 "
          f"cells) and {{a : a mod 64 != 63}} \\ {{0,1,2}} at n = 512 (501 cells), and the "
          f"published saturation tallies 173 and 442 are exactly those sets intersected with "
          f"the published zero-membership sets (188 and 444 cells); no cell is complete over "
          f"{PRIZE_LABEL}, where (p-1)/m > C(n-1,2) excludes completeness by counting; no "
          f"theorem in n or p, no mechanism proved, no t>=4, no global maximum, no "
          f"production regime, no delta* or prize claim", flush=True)


if __name__ == "__main__":
    main()
