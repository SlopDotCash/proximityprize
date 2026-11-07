#!/usr/bin/env python3
"""The pencil (x^2, x^(n-1)) has bad-scalar set EXACTLY mu_n at every prime: count = n.

Object (the published t=3 ceiling monomial-pencil census).  Fix a prime ``p`` with
``n | p - 1``, a generator ``g`` of order ``n`` in ``F_p``, the smooth domain
``x_i = g^i`` and the dimension-two code of affine words ``c0 + c1*x``.  For the
monomial pencil ``(u0, u1) = (x^a, x^b)`` the ceiling (``t = 3``) bad scalars are the
``gamma`` for which ``u0 + gamma*u1`` agrees with an affine word on some triple ``T``
while ``(u0, u1)`` is not jointly affine on ``T``.  With ``D_e(T)`` the collinearity
determinant of ``(1, x, x^e)`` on ``T``, the bad set is exactly
``{ -D_a(T)/D_b(T) : D_b(T) != 0 }``, and writing ``D_e = V_T * h_(e-2)`` with ``V_T``
the Vandermonde product, scaling ``T`` by ``g`` multiplies the ratio by ``g^(a-b)``.
Hence the bad set is a union of cosets of the order-``m`` subgroup,
``m = n / gcd((b-a) mod n, n)``, of size ``m * (#nonzero cosets) + [0 bad]``.

Claim (this probe).  For ``n = 2^k``, ``k >= 3``, and EVERY prime ``p = 1 (mod n)``:

* the exact group-ring identity ``y*z * N_(n-1) - (1-y)(1-z)(y-z) = 0`` in
  ``Z[y,z] / <y^n - 1, z^n - 1>``, where ``N_e = (y-z) + y^e (z-1) + z^e (1-y)``,
  so ``h_(n-3)(1,y,z) = 1/(y z)`` for pairwise distinct ``1, y, z`` in ``mu_n``;
* together with ``h_0 = N_2 / ((1-y)(1-z)(y-z)) == 1`` this pins the pencil
  ``(x^2, x^(n-1))`` to the ratio set ``{-y z}``, which lies in ``mu_n`` (``n`` even),
  and since ``gcd(3-n, n) = 1`` the dilation orbit is all of ``mu_n``;
* therefore the bad-scalar set of ``(x^2, x^(n-1))`` is exactly ``mu_n`` and its count
  is exactly ``n`` -- independent of ``p``; the same holds for the transposed pencil
  ``(x^(n-1), x^2)``; and ``0`` is never a bad scalar for it (``h_0`` never vanishes);
* the same identity route gives the two degenerate rows ``h_(-2) = h_(-1) = 0``, so the
  pencils ``(x^2, 1)`` and ``(x^2, x)`` have an empty bad set (no triple has
  ``D_0`` or ``D_1`` nonzero), and the row ``h_1 = 1 + y + z`` is the ``(x^3, x^2)``
  ceiling stack used as the merged anchor of this probe;
* inside the column ``b = n - 1`` at ``p = 65537`` the value ``n`` is attained by exactly
  one pencil, namely ``a = 2``, both at ``n = 64`` and at ``n = 128`` (the column minimum
  ``1`` occurs at ``a = 0, 1, n - 1`` and the column maximum is ``30784`` at ``n = 64``
  and the absolute ceiling ``65537`` at ``n = 128``).

Engine and anchors.  The bad-scalar counts run through the published shape/coset
engine (the code path of the merged n=16 census, PR #267, and of the n=64/n=128/n=256
censuses, PRs #300/#328/#341): tabulate ``h`` over the ``C(n-1, 2)`` normalised shapes
``{1, y, z}`` through the general closed form and key a ratio by ``ratio^m``.  In-run
reproduction of merged integers, by this engine: the ``(x^3, x^2)`` ceiling count at
``n = 8`` is ``16`` at ``p = 17`` and ``40`` at ``p = 41, 257`` (G310/G328/G330), and at
``n = 16`` it is ``464`` outside the published 34-prime exceptional set and equals the
merged ``CEILING_EXCEPTIONS`` table at all ``279`` primes ``p = 1 (mod 16)`` in
``[17, 20000]``, including ``p = 65537`` and the prize-scale Proth prime ``21*2^128+1``.
The ``n = 512`` cell ``(2,511) = 512`` recorded by the companion a=2/a=3 rows probe of
this campaign (not yet merged) is reproduced here as one instance of the closed form.

Scope (read before citing).  Exact integer arithmetic only, stdlib only, deterministic,
every printed claim hard-asserted.  The ``t = 3`` ceiling semantics of the merged
census, dimension-two affine code, monomial pencils, smooth domains ``mu_n`` with
``n = 2^k``.  The group-ring identity is a proof of the multiplier formula for every
field at the ``n`` values computed here (the certificate is expanded back exactly); it is
NOT a theorem in ``n`` and NOT a statement about any other pencil.  The count ``= n`` is
computed cell by cell at the primes listed; the p-independence is a consequence of the
identity together with the per-cell audit that every ratio lies in ``mu_n``, so it is a
closed form on this family, not an existence result for maximizers.  Nothing here says
anything about ``t >= 4``, about the global maximum at any rung, about the production
regime ``n = 2^30 / 2^32``, about ``delta*``, or about the prize.
"""

import hashlib
import time
from math import gcd, isqrt

LIMIT = 20_000
LADDER = (8, 16, 32, 64, 128, 256, 512, 1024)
FERMAT = 65537
PRIZE_EXP = 128
PRIZE_K = (21, 111, 123)

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

# The n=512 a=2-row cell at p=65537: one instance of the closed form.
N512_65537_CELL = 512

# Column b = n-1 at p = 65537: the a values whose count is exactly n, pinned after the
# first full run -- a = 2 is the unique pencil of the column sitting at the closed form.
COLUMN_CLOSED_FORM = {
    64: (2,),
    128: (2,),
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
    """The published normalised-shape engine: triple shapes and closed-form h rows."""

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
        """h_(exponent-2)(1, y, z) on every shape, always via the closed form."""
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


# ---------------------------------------------------------------------------
# Exact group-ring arithmetic in Z[y, z] / <y^n - 1, z^n - 1>, Laurent-safe:
# because y^n = 1 and z^n = 1 every Laurent monomial is y^i z^j with 0 <= i, j < n.
# Polynomials are dicts {(i, j): integer coefficient}; no floats appear.
# ---------------------------------------------------------------------------

def pmul(a, b, n):
    out = {}
    for (ay, az), ac in a.items():
        if not ac:
            continue
        for (by, bz), bc in b.items():
            if not bc:
                continue
            key = ((ay + by) % n, (az + bz) % n)
            out[key] = out.get(key, 0) + ac * bc
    return {k: v for k, v in out.items() if v}


def padd(*terms):
    out = {}
    for term in terms:
        for key, coeff in term.items():
            out[key] = out.get(key, 0) + coeff
    return {k: v for k, v in out.items() if v}


def psub(a, b):
    return padd(a, {key: -coeff for key, coeff in b.items()})


def monom(i, j, coeff=1, n=None):
    if n is None:
        return {(i, j): coeff}
    return {(i % n, j % n): coeff}


def numerator(exponent, n):
    """N_e = (y - z) + y^e (z - 1) + z^e (1 - y), reduced in the group ring."""
    y = monom(1, 0, n=n)
    z = monom(0, 1, n=n)
    one = monom(0, 0, n=n)
    ye = monom(exponent % n, 0, n=n)
    ze = monom(0, exponent % n, n=n)
    return padd(psub(y, z),
                pmul(ye, psub(z, one), n),
                pmul(ze, psub(one, y), n))


def denominator(n):
    """(1 - y)(1 - z)(y - z) in the group ring."""
    y = monom(1, 0, n=n)
    z = monom(0, 1, n=n)
    one = monom(0, 0, n=n)
    return pmul(pmul(psub(one, y), psub(one, z), n), psub(y, z), n)


def group_ring_identities(n):
    """The five exact identities behind the claim, as zero elements of the group ring."""
    y = monom(1, 0, n=n)
    z = monom(0, 1, n=n)
    one = monom(0, 0, n=n)
    denom = denominator(n)
    checks = {}
    # h_(-2) and h_(-1): the degenerate rows, numerator identically zero.
    checks["N_0 == 0"] = psub(numerator(0, n), {})
    checks["N_1 == 0"] = psub(numerator(1, n), {})
    # h_0 == 1.
    checks["N_2 == denom"] = psub(numerator(2, n), denom)
    # h_1 == 1 + y + z, the (x^3, x^2) stack.
    checks["N_3 == denom*(1+y+z)"] = psub(numerator(3, n),
                                         pmul(denom, padd(one, y, z), n))
    # h_(n-3) == 1/(y z), stated multiplicatively: y z * N_(n-1) == denom.
    checks["y*z*N_(n-1) == denom"] = psub(pmul(pmul(y, z, n), numerator(n - 1, n), n),
                                         denom)
    for label, poly in checks.items():
        assert poly == {}, (n, label, sorted(poly.items())[:6])
    return checks


def main():
    start = time.time()
    fermat_ok = FERMAT == 2 ** 16 + 1 and is_prime(FERMAT)
    assert fermat_ok
    prize_primes = {}
    witnesses = {}
    for k in PRIZE_K:
        value, witness = proth_prime(k, PRIZE_EXP)
        prize_primes[k] = value
        witnesses[k] = witness
    print(f"p = {FERMAT} = 2^16 + 1 prime; prize-scale Proth primes "
          f"{', '.join(f'{k}*2^128+1 (Proth witness a={witnesses[k]})' for k in PRIZE_K)}",
          flush=True)

    # 1. Merged integers reproduced by this engine: the (x^3, x^2) t=3 ceiling count.
    n8_primes = primes_one_mod(8, LIMIT)
    n16_primes = primes_one_mod(16, LIMIT)
    assert len(n16_primes) == N16_PRIMES_COUNT and n16_primes[0] == 17
    profile16 = {}
    for index, p in enumerate(n16_primes):
        shapes = Shapes(16, p)
        count, m, cosets, zero = shapes.t3(3, 2)
        assert m == 16, (p, m)
        assert count == 16 * cosets + (1 if zero else 0), (p, count, cosets, zero)
        profile16[p] = count
        if index % 40 == 0:
            print(f"  n=16 anchor: {index + 1}/{len(n16_primes)} primes (last p={p})",
                  flush=True)
    for p, expected in CEILING_EXCEPTIONS.items():
        assert profile16[p] == expected, (p, profile16[p], expected)
    exceptions = sorted(p for p, count in profile16.items() if count != N16_CEILING_DEFAULT)
    assert exceptions == sorted(CEILING_EXCEPTIONS), exceptions
    n8_profile = {}
    for p in n8_primes:
        n8_profile[p] = Shapes(8, p).t3(3, 2)[0]
    for p, expected in N8_CEILING.items():
        assert n8_profile[p] == expected, (p, n8_profile[p], expected)
    n8_split = sorted((p, c) for p, c in n8_profile.items() if c != 40)
    assert n8_split == [(17, 16)], n8_split
    print(f"merged anchors reproduced by the shape engine: n=8 (x^3,x^2) t=3 ceiling "
          f"40 at every one of the {len(n8_primes)} primes p = 1 (mod 8) in [17, {LIMIT}] "
          f"except p=17 ({n8_profile[17]}), the G330 exact boundary; n=16 ceiling "
          f"{N16_CEILING_DEFAULT} at {len(n16_primes) - len(exceptions)} of the "
          f"{len(n16_primes)} primes p = 1 (mod 16) in [17, {LIMIT}], exceptions "
          f"{len(exceptions)} primes exactly as the merged table", flush=True)
    shapes65537_16 = Shapes(16, FERMAT)
    assert shapes65537_16.t3(3, 2)[0] == 464
    assert Shapes(16, prize_primes[21]).t3(3, 2)[0] == 464
    print(f"merged n=16 spot values at p = {FERMAT} and at the prize-scale prime "
          f"21*2^128+1: ceiling 464 in both", flush=True)

    # 2. Exact group-ring identities at every rung of the ladder.
    for n in LADDER:
        group_ring_identities(n)
    print(f"group-ring identities (h_(-2)=h_(-1)=0, h_0=1, h_1=1+y+z, "
          f"y*z*N_(n-1)=denom) verified as exact zero elements for n in {LADDER}",
          flush=True)

    # 3. The closed form, cell by cell: count(x^2, x^(n-1)) = n = |mu_n|, p-independent.
    cells = []
    failures = []
    small_primes = {}
    for n in LADDER:
        found = []
        candidate = n + 1
        while len(found) < 3 and candidate < 4_000_000:
            if is_prime(candidate) and candidate % n == 1:
                found.append(candidate)
            candidate += n
        assert len(found) == 3, n
        small_primes[n] = found
    grid = []
    for n in LADDER:
        for p in small_primes[n] + [FERMAT] + [prize_primes[k] for k in PRIZE_K]:
            grid.append((n, p))
    for index, (n, p) in enumerate(grid):
        shapes = Shapes(n, p)
        assert len(shapes.pairs) == (n - 1) * (n - 2) // 2
        # The identity, audited on every shape of this cell through the closed form.
        row2 = shapes.row(2)
        row_nm1 = shapes.row(n - 1)
        ys, zs = shapes.ys, shapes.zs
        assert all(value == 1 for value in row2), (n, p)
        assert all((row_nm1[i] * ys[i] % p) * zs[i] % p == 1
                   for i in range(len(ys))), (n, p)
        count, m, cosets, zero = shapes.t3(2, n - 1, row_a=row2, row_b=row_nm1)
        swap, m_swap, cosets_swap, zero_swap = shapes.t3(n - 1, 2, row_a=row_nm1,
                                                        row_b=row2)
        every_ratio_in_domain = True
        nonzero_ratios = 0
        inv_b = batch_inverse(row_nm1, p)
        for i, value in enumerate(row_nm1):
            if value:
                ratio = (-row2[i] * inv_b[i]) % p
                nonzero_ratios += 1
                if pow(ratio, n, p) != 1:
                    every_ratio_in_domain = False
        ok = (count == n and swap == n and m == n and m_swap == n and cosets == 1
              and cosets_swap == 1 and not zero and not zero_swap
              and every_ratio_in_domain and nonzero_ratios == len(shapes.pairs))
        cells.append((n, p, count, swap))
        if not ok:
            failures.append((n, p, count, swap, m, cosets, zero))
        if index % 10 == 0:
            print(f"  closed-form grid: {index + 1}/{len(grid)} cells (last n={n}, "
                  f"p={p if p < 100000 else f'{p >> 128}*2^128+1'})", flush=True)
    assert not failures, failures[:4]
    digest = sum(count for _, _, count, _ in cells)
    swap_digest = sum(swap for _, _, _, swap in cells)
    expected_digest = sum(n for n, _, _, _ in cells)
    assert digest == swap_digest == expected_digest, (digest, swap_digest, expected_digest)
    vector = ";".join(f"{n},{p if p < 10 ** 6 else 'P' + str(p >> 128)},{count},{swap}"
                      for n, p, count, swap in cells)
    sha = hashlib.sha256(vector.encode()).hexdigest()
    print(f"count(x^2, x^(n-1)) = count(x^(n-1), x^2) = n at every cell of the grid: "
          f"{len(cells)} cells over n in {LADDER} x {len(grid) // len(LADDER)} primes "
          f"each (three smallest p = 1 (mod n), the Fermat prime 65537, and the three "
          f"prize-scale Proth primes); count digest {digest}, transposed digest "
          f"{swap_digest}, vector sha256 {sha}",
          flush=True)
    print(f"per-rung counts at p = {FERMAT}: "
          + ", ".join(f"n={n}: {count}" for n, p, count, _ in cells if p == FERMAT),
          flush=True)

    # 4. The n = 512 a = 2 row cell at 65537 is one instance of the closed form.
    shapes512 = Shapes(512, FERMAT)
    deepest, m512, cosets512, zero512 = shapes512.t3(2, 511)
    assert (deepest, m512, cosets512, zero512) == (N512_65537_CELL, 512, 1, False)
    print(f"deepest cell: n=512, p={FERMAT}, pencil (x^2, x^511) count {deepest} = "
          f"n = |mu_512|: the a=2 row deficit of the n=512 census is this closed form "
          f"at n=512", flush=True)

    # 5. Column b = n-1 at 65537: which a-values the closed form reaches.
    for n in (64, 128):
        shapes = Shapes(n, FERMAT)
        row_b = shapes.row(n - 1)
        counts = {}
        for a in range(n):
            counts[a] = shapes.t3(a, n - 1, row_b=row_b)[0]
        exact_n = tuple(sorted(a for a, count in counts.items() if count == n))
        pinned = COLUMN_CLOSED_FORM[n]
        if pinned is not None:
            assert exact_n == pinned, (n, exact_n, pinned)
        assert counts[2] == n
        assert 2 in exact_n
        print(f"column b = {n - 1} at p = {FERMAT}: count = n exactly at a in {exact_n} "
              f"(includes the closed form a = 2); column min {min(counts.values())}, "
              f"max {max(counts.values())}, sum {sum(counts.values())}", flush=True)

    print(f"PASS: exact closed form -- the t=3 ceiling bad-scalar set of the pencil "
          f"(x^2, x^(n-1)) is mu_n itself, count n, at all {len(cells)} (n, p) cells; "
          f"no production-regime, t>=4, global-maximum, delta* or prize claim",
          flush=True)
    print(f"elapsed {time.time() - start:.1f}s", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
