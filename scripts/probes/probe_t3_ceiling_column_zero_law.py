#!/usr/bin/env python3
# Copyright (c) 2026 safwaankira. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
# Authors: safwaankira
"""Zero-membership law of the ``t = 3`` ceiling column ``b = n - 1``, at every ``n``.

The merged probe ``probe_t3_ceiling_column_non2power.py`` reports that the staged two-power
law ``L-zero`` ("``0`` is a bad scalar exactly at ``a = 0 or 1 (mod 4)``") fails at all 212
of its non-two-power cells with ``n >= 8``, and that the law "holds with the modulus moved"
at some rungs.  This probe states the replacement law for every ``n``, records which parts of
it are proved and which are computed, and checks all of it exactly.

Setting.  ``K`` is a field containing the group ``mu_n`` of ``n`` distinct ``n``-th roots of
unity, ``n >= 3``, and ``0 <= a <= n - 1``.  Write ``[x0, x1, x2] f`` for the second divided
difference; the census row is ``h_(a-2)(x0, x1, x2) = [x0, x1, x2] x^a``.  In the column
``b = n - 1`` the denominator row is ``[x0, x1, x2] x^(-1) = 1 / (x0 x1 x2)``, never zero, so

    ``0`` is a bad scalar of the pencil ``(x^a, x^(n-1))``
        iff  some three distinct points of ``mu_n`` have ``[x0, x1, x2] x^a = 0``
        iff  ``f_a(y) = f_a(z)`` for some distinct ``y, z`` in ``mu_n \\ {1}``,

where ``f_a(x) = 1 + x + ... + x^(a-1)`` (dilate to ``x0 = 1``; then
``[1, y, z] x^a = (f_a(y) - f_a(z)) / (y - z)``).  Call the set of such ``a`` ``Z_K(n)``, and

    ``LAW(n) = { a in [0, n-1] : gcd(a, n) >= 3  or  gcd(a - 1, n) >= 3 }``

(with ``gcd(0, n) = n``).  At ``n = 2^k >= 4`` this is ``a = 0 or 1 (mod 4)``, the staged law.

What is proved (pen-and-paper proofs below; no Lean theorem is claimed in this file):

* ``T1`` (every ``K``): ``LAW(n)`` is contained in ``Z_K(n)``.
  If ``d = gcd(a, n) >= 3`` then ``x^a = 1`` on ``mu_d``; if ``d = gcd(a - 1, n) >= 3`` then
  ``x^a = x`` on ``mu_d``.  Either way ``x^a`` is affine on three distinct points.
* ``T2`` (``K = C``): ``Z_C(n) = LAW(n)``.
  Let ``|y| = |z| = 1``, ``y, z, 1`` distinct ``n``-th roots, ``f_a(y) = f_a(z) = V``.
  If ``V = 0`` then ``y^a = z^a = 1``, so ``1, y, z`` lie in ``mu_gcd(a,n)`` and
  ``gcd(a, n) >= 3``.  If ``V != 0``: on the unit circle ``conj(f_a(x)) = x^(1-a) f_a(x)``, so
  ``y^(a-1) = V / conj(V) = z^(a-1)`` and ``w = y / z != 1`` lies in ``mu_g``,
  ``g = gcd(a - 1, n)``.  If ``g >= 3`` we are done.  Otherwise ``g = 2``, ``z = -y``, ``a`` is
  odd, and ``(y - 1)((-y)^a - 1) = (-y - 1)(y^a - 1)`` expands to ``y^(a-1) = 1``, i.e.
  ``y = +-1``, which forces ``{y, z} = {1, -1}``: contradiction.
* ``T3`` (``K = F_p``, ``p = 1 (mod n)``, ``p > 6^phi(n)``): ``Z_K(n) = LAW(n)``.
  For exponents ``u, v`` the obstruction is the six-term sum
  ``D = zeta^(u+va) - zeta^u - zeta^(va) - zeta^(v+ua) + zeta^v + zeta^(ua)`` in ``Z[zeta_n]``.
  Reduction mod a prime over ``p`` kills ``D`` only if ``p`` divides the norm ``N(D)``, and
  ``D != 0`` gives ``1 <= |N(D)| <= 6^phi(n)``.
* ``T4`` (every ``K``; this is the staged law ``L-min`` as a theorem in ``n`` and ``K``): the
  column count is ``1`` at ``a in {0, 1, n-1}``, and at ``2 <= a <= n - 2`` it is at least
  ``n / gcd(a + 1, n) >= 2``.  (At ``a = 0, 1`` every scalar is ``0``; at ``a = n - 1`` every
  scalar is ``-1``.  Otherwise ``x^a`` is not affine on ``mu_n`` because ``x^a - cx - d`` has
  degree ``a < n``, so some scalar ``s`` is nonzero, and dilation by ``c`` in ``mu_n`` maps it
  to ``c^(a+1) s``.)
* ``T5`` (every ``K``, ``n >= 4``): the column count at ``a = 2`` is exactly ``n`` (the scalars
  are ``-x0 x1 x2``, and products of three distinct elements cover ``mu_n`` once ``n >= 4``).
  The uniqueness half of the staged law ``L-countn`` is NOT proved here.

What is computed (exact integer arithmetic, stdlib only, deterministic, byte-reproducible):

1. Reproduction first: on every cell of the merged probe's grid, the zero flags of the merged
   engine equal the geometric-sum collision test used here (a different formula, no
   inverses), and ``T1``, ``T4``, ``T5`` hold there.
2. ``T3`` cells: for every ``n`` in ``3..128`` and the two-power rungs ``256, 512, 1024``, at a
   Proth-certified prime ``p = 1 (mod n)`` with ``p > 6^phi(n)``, ``Z = LAW(n)`` exactly.  By
   the norm bound each such cell is also a proof-independent exact check of ``T2`` at that
   ``n``.
3. Exception inventory: for every ``n`` in ``3..64`` and every prime ``p = 1 (mod n)`` up to
   ``20000``, whether ``Z`` equals ``LAW(n)``, with the largest exceptional prime per rung.

Scope, read before citing.  One column (``b = n - 1``) of one threshold (``t = 3``) of the
monomial-pencil census on ``mu_n``.  The bound ``6^phi(n)`` in ``T3`` is astronomically above
every deployed field at the production rungs ``n = 2^30 / 2^32``: there, only the inclusion
``T1`` and the count statements ``T4``/``T5`` are theorems, and item 3 shows the converse
inclusion does fail at small primes.  Nothing here is about another column, ``t >= 4``, the
column maximum (``L-max`` stays open), global census maxima, ``delta*``, or the prize.
"""

import hashlib
import os
import sys
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import probe_t3_ceiling_column_non2power as merged  # noqa: E402

T3_N_MIN, T3_N_MAX = 3, 128
T3_EXTRA_RUNGS = (256, 512, 1024)
INVENTORY_N_MIN, INVENTORY_N_MAX = 3, 64
INVENTORY_LIMIT = merged.LIMIT
PROTH_WITNESSES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)

# Pinned totals of the 2026-11-10 run; a change of data cannot pass silently.
GRID_CELLS, GRID_EQUAL = 252, 120
T3_RUNGS = 129
INVENTORY_CELLS, INVENTORY_EXCEPTIONAL = 13525, 572
INVENTORY_CLEAN_RUNGS = [3, 4, 5, 6, 7, 8, 9, 12, 15, 24]


def require(condition, message):
    """Hard gate that stays active under ``python -O`` / ``-OO``."""
    if not condition:
        raise AssertionError(message)


def zero_law(n):
    """LAW(n): gcd(a, n) >= 3 or gcd(a - 1, n) >= 3, for a in [0, n-1]."""
    require(n >= 3, f"n={n} < 3")
    return tuple(a for a in range(n)
                 if gcd(a, n) >= 3 or gcd((a - 1) % n, n) >= 3)


def totient(n):
    result = n
    for prime in merged.prime_factors(n):
        result -= result // prime
    return result


def zero_set(n, p, generator):
    """Z_K(n) over F_p by collisions of f_a(x) = 1 + x + ... + x^(a-1) on mu_n minus {1}.

    Running sums only: no inverses and no divided-difference rows, so this shares no
    arithmetic with ``merged.Shapes``.
    """
    require(pow(generator, n, p) == 1, f"generator order does not divide {n}")
    points = [pow(generator, exponent, p) for exponent in range(1, n)]
    require(len(set(points)) == n - 1 and 1 not in points,
            f"generator is not of exact order {n} modulo p")
    sums = [0] * (n - 1)
    powers = [1] * (n - 1)
    members = []
    for a in range(n):
        # here sums[i] = f_a(points[i]) and powers[i] = points[i]^a
        if len(set(sums)) < n - 1:
            members.append(a)
        sums = [(s + w) % p for s, w in zip(sums, powers)]
        powers = [w * x % p for w, x in zip(powers, points)]
    return tuple(members)


def proth_prime_above(n, floor):
    """Smallest-exponent Proth prime k*2^e + 1 = 1 (mod n) above ``floor``.

    Certified in-run by Proth's theorem (k odd, k < 2^e, witness w with
    w^((N-1)/2) = -1 mod N).  Returns (prime, k, e, witness).
    """
    odd = merged.odd_part(n)
    two_part = n // odd
    exponent = max(floor.bit_length() + 1, two_part.bit_length() - 1, odd.bit_length() + 1)
    while True:
        k = odd
        while k < (1 << exponent) and k < odd * 20000:
            candidate = (k << exponent) + 1
            if candidate > floor and all(candidate % q for q in (3, 5, 7, 11, 13)):
                for witness in PROTH_WITNESSES:
                    if pow(witness, (candidate - 1) // 2, candidate) == candidate - 1:
                        require(k % 2 == 1 and k < (1 << exponent), "Proth shape")
                        require((candidate - 1) % n == 0, "p = 1 (mod n)")
                        return candidate, k, exponent, witness
            k += 2 * odd
        exponent += 1


def short(values):
    return hashlib.sha256(",".join(str(v) for v in values).encode()).hexdigest()[:16]


def reproduce_merged_grid():
    """Item 1: merged engine vs collision test on the merged grid; T1, T4, T5 there."""
    rungs = sorted(set(range(merged.N_MIN, merged.N_MAX + 1)) | set(merged.CONTROL_EXTRA_RUNGS))
    cells = equal = 0
    digests = []
    for n in rungs:
        law = zero_law(n)
        primes = merged.primes_one_mod(n, 3) + [merged.proth_prime_one_mod(n)[0]]
        for p in primes:
            shapes = merged.Shapes(n, p)
            counts, profile = shapes.column(n - 1)
            engine_zero = tuple(a for a in range(n) if profile[a][2])
            direct_zero = zero_set(n, p, shapes.generator)
            require(engine_zero == direct_zero,
                    f"n={n} p={p}: merged engine {engine_zero} != collision test {direct_zero}")
            require(set(law) <= set(direct_zero), f"T1 fails at n={n} p={p}")
            for a in sorted({0, 1, n - 1}):
                require(counts[a] == 1, f"T4 fails at n={n} p={p} a={a}: {counts[a]}")
            for a in range(2, n - 1):
                floor = n // gcd(a + 1, n)
                require(counts[a] >= floor >= 2,
                        f"T4 floor fails at n={n} p={p} a={a}: {counts[a]} < {floor}")
            if n >= 4:
                require(counts[2] == n, f"T5 fails at n={n} p={p}: {counts[2]}")
            cells += 1
            equal += direct_zero == law
            digests.append(short(direct_zero))
    return cells, equal, short(digests)


def t3_cells():
    """Item 2: Z = LAW(n) at a certified prime above 6^phi(n)."""
    rungs = list(range(T3_N_MIN, T3_N_MAX + 1)) + list(T3_EXTRA_RUNGS)
    records = []
    for n in rungs:
        floor = 6 ** totient(n)
        p, k, exponent, witness = proth_prime_above(n, floor)
        require(p > floor, f"n={n}: prime not above the norm bound")
        generator = merged.order_element(p, n)
        found = zero_set(n, p, generator)
        law = zero_law(n)
        require(found == law,
                f"T3 cell fails at n={n} p={k}*2^{exponent}+1: "
                f"extra={sorted(set(found) - set(law))} "
                f"missing={sorted(set(law) - set(found))}")
        records.append((n, k, exponent, witness, len(law), short(law)))
    return records


def inventory():
    """Item 3: where Z = LAW(n) among all primes p = 1 (mod n) up to the limit."""
    rows = []
    for n in range(INVENTORY_N_MIN, INVENTORY_N_MAX + 1):
        law = zero_law(n)
        primes = merged.primes_one_mod(n)
        exceptional = []
        for p in primes:
            found = zero_set(n, p, merged.order_element(p, n))
            require(set(law) <= set(found), f"T1 fails at n={n} p={p}")
            if found != law:
                exceptional.append(p)
        rows.append((n, len(primes), exceptional))
    return rows


def main():
    print("zero-membership law of the t=3 ceiling column b = n-1")
    print("LAW(n) = { a : gcd(a,n) >= 3 or gcd(a-1,n) >= 3 }")
    for n in (4, 8, 16, 32, 64, 128, 256, 512, 1024):
        require(zero_law(n) == tuple(a for a in range(n) if a % 4 in (0, 1)),
                f"LAW({n}) is not the staged mod-4 law")
    print("two-power rungs 4..1024: LAW(n) is exactly a = 0 or 1 (mod 4)")

    print()
    cells, equal, grid_digest = reproduce_merged_grid()
    require((cells, equal) == (GRID_CELLS, GRID_EQUAL),
            f"merged-grid totals moved: {(cells, equal)}")
    print(f"item 1, merged grid: {cells} cells; merged engine zero flags = collision test at "
          f"{cells}/{cells}; T1, T4, T5 hold at {cells}/{cells}")
    print(f"  Z = LAW(n) at {equal}/{cells} merged-grid cells (small primes carry extra "
          f"zeros; see item 3); zero-set digest {grid_digest}")

    print()
    records = t3_cells()
    require(len(records) == T3_RUNGS, f"T3 rung count moved: {len(records)}")
    print(f"item 2, T3 cells: Z = LAW(n) at {len(records)}/{len(records)} rungs "
          f"(n = {T3_N_MIN}..{T3_N_MAX} and {', '.join(str(n) for n in T3_EXTRA_RUNGS)}), "
          "each at a Proth-certified prime p = 1 (mod n) with p > 6^phi(n)")
    for n, k, exponent, witness, size, law_digest in records:
        print(f"T3CELL n={n} p={k}*2^{exponent}+1 witness={witness} |LAW|={size} "
              f"law={law_digest}")

    print()
    rows = inventory()
    total = sum(count for _, count, _ in rows)
    bad = sum(len(exceptional) for _, _, exceptional in rows)
    print(f"item 3, inventory: n = {INVENTORY_N_MIN}..{INVENTORY_N_MAX}, all primes "
          f"p = 1 (mod n) up to {INVENTORY_LIMIT}: {total} cells, Z = LAW(n) at "
          f"{total - bad}, Z strictly larger at {bad}")
    for n, count, exceptional in rows:
        largest = exceptional[-1] if exceptional else "-"
        print(f"INV n={n} primes={count} exceptional={len(exceptional)} largest={largest} "
              f"set={short(exceptional)}")
    clean = [n for n, _, exceptional in rows if not exceptional]
    require((total, bad) == (INVENTORY_CELLS, INVENTORY_EXCEPTIONAL),
            f"inventory totals moved: {(total, bad)}")
    require(clean == INVENTORY_CLEAN_RUNGS, f"clean rungs moved: {clean}")
    print(f"rungs with no exceptional prime up to {INVENTORY_LIMIT}: {clean}")

    print()
    print("PASS")


if __name__ == "__main__":
    main()
