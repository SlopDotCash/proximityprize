#!/usr/bin/env python3
# Copyright (c) 2026 laooooonn. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
# Authors: laooooonn (GitHub: andyboss1995)
"""Independent crosscheck of the ``t = 3`` ceiling column ``b = n - 1`` at non-two-power rungs.

Second implementation of the SAME grid as ``probe_t3_ceiling_column_non2power.py``, with no
shared algebraic path: it enumerates ALL ``C(n, 3)`` distinct triples of ``mu_n`` and forms the
bad scalar of a triple directly as the ratio of two ``3 x 3`` collinearity determinants

    det[[1,1,1], [x_i,x_j,x_k], [u0_i,u0_j,u0_k] + g * [u1_i,u1_j,u1_k]] = 0
    =>  gamma(S) = -A(S) / B(S),   A = det(1, x, u0),  B = det(1, x, u1),

expanded by cofactors of the ``(1, x)`` rows (so ``B`` and the cofactors are computed ONCE per
column, because they depend only on ``b``, and each ``a`` costs three table lookups per triple).
It uses no normalised-shape reduction, no ``h``-row closed form, no dilation orbit, no
``gamma^m`` coset keying, and no discrete logarithms.  The bad set of the pencil is then

    bad(a, b) = { gamma(S) : S a triple with B(S) != 0 },      count = |bad|,

which is asserted to coincide with the merged definition (candidate triples plus line buckets
plus the joint-affineness exclusion of ``probe_n16_below_ceiling_max.py``) on every cell of the
``n <= 12`` sub-grid, so the simplification is checked and not assumed.

Reproduced first: the merged ``(x^3, x^2)`` ceiling integers at ``n = 8`` (``40``, and ``16`` at
``p = 17``) and ``n = 16`` (``464`` outside the merged 34-prime exception set) through this
determinant route, and the campaign's UNMERGED staged two-power column digests.

Exact integer arithmetic, stdlib only, deterministic, no timing printed; exit ``0`` means
``PASS``.  Same scope limits as the primary probe: a finite-field census of one column at one
threshold on ``mu_n``, not a theorem, not ``t >= 4``, not another column, not a global maximum,
not the production regime, not ``delta*``, not the prize.
"""

import hashlib
from itertools import combinations
from math import gcd

LIMIT = 20_000
FERMAT = 65537
PRIZE_EXP = 128
PRIZE_K = 21
PROTH_E_MIN, PROTH_E_MAX, PROTH_K_MULT_MAX = 11, 45, 99
N_MIN, N_MAX = 3, 64
CONTROL_EXTRA_RUNGS = (128,)
FULL_DEFINITIONS_UPTO = 64          # full column by the determinant route
MERGED_ROUTE_UPTO = 12              # full column also by the merged bucket definition
N8_CEILING_DEFAULT, N8_CEILING_EXCEPTIONS = 40, {17: 16}
N16_CEILING_DEFAULT = 464
N16_CEILING_EXCEPTIONS = {
    17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
    353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
    673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
    1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
    1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
    4001: 448, 4049: 448,
}
N8_PRIME_COUNT, N16_PRIME_COUNT, N16_EXCEPTION_COUNT = 556, 279, 34


def sieve(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[0] = flags[1] = 0
    index = 2
    while index * index <= limit:
        if flags[index]:
            step = index * index
            flags[step::index] = bytearray(len(range(step, limit + 1, index)))
        index += 1
    return [value for value in range(limit + 1) if flags[value]]


PRIMES = sieve(LIMIT)


def primes_one_mod(mod, count=None):
    found = [p for p in PRIMES if (p - 1) % mod == 0]
    return found if count is None else found[:count]


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def two_power_exponent(n):
    rest, exponent = n, 0
    while n and rest % 2 == 0:
        rest //= 2
        exponent += 1
    return exponent if rest == 1 else None


def proth_prime_one_mod(n):
    odd = odd_part(n)
    v2 = n // odd
    for e in range(max(PROTH_E_MIN, v2.bit_length() - 1), PROTH_E_MAX + 1):
        for multiple in range(1, PROTH_K_MULT_MAX + 1, 2):
            k = odd * multiple
            if k >= (1 << e):
                break
            if (k << e) % n:
                continue
            candidate = (k << e) + 1
            for witness in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
                if pow(witness, (candidate - 1) // 2, candidate) == candidate - 1:
                    return candidate, k, e, witness
    raise AssertionError(f"no Proth prime for n={n}")


def prime_factors(value):
    out, divisor = [], 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            out.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    return out + ([value] if value > 1 else [])


def order_element(p, n):
    if (p - 1) % n:
        raise AssertionError(f"{n} does not divide p-1")
    factors = prime_factors(n)
    for candidate in range(2, p):
        element = pow(candidate, (p - 1) // n, p)
        if element != 1 and all(pow(element, n // f, p) != 1 for f in factors):
            return element
    raise AssertionError(f"no element of order {n} mod {p}")


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


class Determinants:
    """Raw triple collinearity determinants on mu_n: no shapes, no rows, no keying."""

    def __init__(self, n, p):
        self.n, self.p = n, p
        g = order_element(p, n)
        self.xs = [pow(g, k, p) for k in range(n)]
        assert len(set(self.xs)) == n
        self.triples = list(combinations(range(n), 3))
        # Cofactors of the (1, x) rows: D_e(S) = ci*u_e_i + cj*u_e_j + ck*u_e_k.
        self.cof = [((self.xs[k] - self.xs[j]) % p,
                     (self.xs[i] - self.xs[k]) % p,
                     (self.xs[j] - self.xs[i]) % p)
                    for (i, j, k) in self.triples]

    def powers(self, exponent):
        n, xs = self.n, self.xs
        return [xs[(index * exponent) % n] for index in range(n)]

    def det(self, exponent):
        """3x3 determinant D_e(S) = det(1, x, x^e) on every triple."""
        u = self.powers(exponent)
        out = []
        for position, (i, j, k) in enumerate(self.triples):
            ci, cj, ck = self.cof[position]
            out.append((ci * u[i] + cj * u[j] + ck * u[k]) % self.p)
        return out

    def bad_set(self, a, b, det_b=None, inv_b=None):
        """The literal bad-scalar set of the pencil (x^a, x^b) at threshold t = 3."""
        det_b = self.det(b) if det_b is None else det_b
        inv_b = batch_inverse(det_b, self.p) if inv_b is None else inv_b
        det_a = self.det(a)
        bad = set()
        add = bad.add
        for index, denominator in enumerate(det_b):
            if denominator:
                add((-det_a[index] * inv_b[index]) % self.p)
        return bad

    def column(self, b, a_list=None):
        det_b = self.det(b)
        inv_b = batch_inverse(det_b, self.p)
        counts, zeros = {}, {}
        for a in (range(self.n) if a_list is None else a_list):
            bad = self.bad_set(a, b, det_b, inv_b)
            counts[a] = len(bad)
            zeros[a] = 0 in bad
        return counts, zeros

    # ---- the merged definition, verbatim, used only to validate the simplification ----
    def merged_bad_set(self, a, b):
        p, n = self.p, self.n
        u0, u1 = self.powers(a), self.powers(b)
        xs = self.xs
        pair_inv = {(i, j): pow((xs[j] - xs[i]) % p, -1, p)
                    for i, j in combinations(range(n), 2)}
        candidates = set()
        for (i, j, k) in self.triples:
            a11, a12 = (u1[j] - u1[i]) % p, (xs[i] - xs[j]) % p
            a21, a22 = (u1[k] - u1[i]) % p, (xs[i] - xs[k]) % p
            det = (a11 * a22 - a12 * a21) % p
            if det:
                b1, b2 = (u0[j] - u0[i]) % p, (u0[k] - u0[i]) % p
                candidates.add((((-b1) * a22 - a12 * (-b2)) % p) * pow(det, -1, p) % p)
        bad = set()
        for gamma in candidates:
            values = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
            lines = {}
            for i, j in combinations(range(n), 2):
                slope = (values[j] - values[i]) * pair_inv[(i, j)] % p
                intercept = (values[i] - slope * xs[i]) % p
                lines.setdefault((slope, intercept), []).append((i, j))
            for (slope, intercept), pairs in lines.items():
                if len(pairs) < 3:
                    continue
                witness = [t for t in range(n)
                           if (intercept + slope * xs[t] - values[t]) % p == 0]
                if len(witness) < 3:
                    continue
                def affine_on(u, points):
                    first, second = points[0], points[1]
                    slope = ((u[second] - u[first])
                             * pow((xs[second] - xs[first]) % p, -1, p)) % p
                    intercept = (u[first] - slope * xs[first]) % p
                    return all((intercept + slope * xs[t] - u[t]) % p == 0 for t in points)
                if not (affine_on(u0, witness) and affine_on(u1, witness)):
                    bad.add(gamma)
                    break
        return bad


def digest(counts):
    n = len(counts)
    return hashlib.sha256(
        ",".join(str(counts[a]) for a in range(n)).encode()).hexdigest()


def label(p):
    if p == FERMAT:
        return "65537"
    if p == PRIZE_K * (1 << PRIZE_EXP) + 1:
        return f"{PRIZE_K}*2^128+1"
    return str(p)


def main():
    print("crosscheck: t=3 ceiling column b = n-1 by raw triple collinearity determinants")
    prize = PRIZE_K * (1 << PRIZE_EXP) + 1

    # ---- merged anchors through the determinant route -------------------------------
    matched8 = 0
    for p in primes_one_mod(8):
        engine = Determinants(8, p)
        size = len(engine.bad_set(3, 2))
        assert size == N8_CEILING_EXCEPTIONS.get(p, N8_CEILING_DEFAULT), (p, size)
        matched8 += 1
    assert matched8 == N8_PRIME_COUNT
    print(f"anchor n=8: {matched8} primes, determinant route reproduces "
          f"{N8_CEILING_DEFAULT} (and {N8_CEILING_EXCEPTIONS}) entry by entry")
    table16 = {}
    for p in primes_one_mod(16):
        engine = Determinants(16, p)
        table16[p] = len(engine.bad_set(3, 2))
    assert len(table16) == N16_PRIME_COUNT
    for p, value in table16.items():
        assert value == N16_CEILING_EXCEPTIONS.get(p, N16_CEILING_DEFAULT), (p, value)
    assert sorted(p for p in table16 if p in N16_CEILING_EXCEPTIONS) == \
        sorted(N16_CEILING_EXCEPTIONS)
    print(f"anchor n=16: {len(table16)} primes reproduced, merged "
          f"{N16_EXCEPTION_COUNT}-prime exception set matched exactly")

    # ---- simplification check against the merged definition, verbatim ----------------
    checked = 0
    for n in range(N_MIN, MERGED_ROUTE_UPTO + 1):
        for p in primes_one_mod(n, 3):
            engine = Determinants(n, p)
            for a in range(n):
                fast = engine.bad_set(a, n - 1)
                slow = engine.merged_bad_set(a, n - 1)
                assert fast == slow, (n, p, a, len(fast), len(slow))
                checked += 1
    print(f"merged-definition check (candidate triples + line buckets + joint-affineness "
          f"exclusion): {checked} cells at n <= {MERGED_ROUTE_UPTO}, SET-IDENTICAL to the "
          f"determinant route")

    # ---- staged two-power columns (campaign's own UNMERGED digests) ------------------
    staged = {
        (8, "65537"): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
        (16, "65537"): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
        (32, "65537"): "3cce569863d7fdac3b3c966abcb1c1344bbe0419121e58bdfadb3f0bea11c961",
        (64, "65537"): "69f3e4c5416969ea428cf7fb0e96abd83ba6f6fc3ea11a9932313dfe6d5dfa1c",
        (128, "65537"): "5630704e234513e22d52b9d06f0bb46c3905869e5d675ec99f2194f2be3a8211",
    }
    for (n, tag), expected in sorted(staged.items()):
        engine = Determinants(n, FERMAT)
        counts, _ = engine.column(n - 1)
        assert digest(counts) == expected, (n, tag)
    print("staged two-power columns at 65537 (n=8,16,32,64,128): determinant route "
          "reproduces the campaign's unmerged staged digests")

    # ---- the grid --------------------------------------------------------------------
    rungs = list(range(N_MIN, N_MAX + 1)) + list(CONTROL_EXTRA_RUNGS)
    rows = []
    for n in rungs:
        small = primes_one_mod(n, 3)
        large, k_proth, e_proth, witness = proth_prime_one_mod(n)
        sample = None
        if n > FULL_DEFINITIONS_UPTO:
            sample = sorted(set(list(range(0, 11)) + [n - 3, n - 2, n - 1]))
        for p in small + [large]:
            engine = Determinants(n, p)
            if sample is None:
                counts, zeros = engine.column(n - 1)
                full = True
            else:
                partial, zeros = engine.column(n - 1, sample)
                counts = {a: partial[a] for a in sample}
                full = False
            values = [counts[a] for a in (range(n) if full else sample)]
            rows.append({
                "n": n, "tag": label(p), "full": full, "zeros": zeros,
                "cells": len(values), "total": sum(values), "biggest": max(values),
                "exact_n": [a for a in (range(n) if full else sample) if counts[a] == n],
                "min_at_zero": counts[0] == 1 and counts[1] == 1 and counts[n - 1] == 1,
                "digest": digest(counts) if full else "",
                "counts": counts,
            })
    full_rows = [r for r in rows if r["full"]]
    print()
    print("per-cell records (digest is the first 16 hex of the sha256 of the comma-"
          "separated count vector in a = 0..n-1 order, same convention as the primary "
          "probe):")
    for r in rows:
        if r["full"]:
            print(f"CELL n={r['n']} p={r['tag']} sum={r['total']} max={r['biggest']} "
                  f"zero={sum(1 for a in range(r['n']) if r['zeros'][a])} "
                  f"exactn={len(r['exact_n'])} digest={r['digest'][:16]}")
        else:
            pairs = ";".join(f"{a}:{r['counts'][a]}" for a in sorted(r["counts"]))
            print(f"SAMPLE n={r['n']} p={r['tag']} pairs={pairs}")
    print()
    print(f"grid: {len(rows)} cells ({len(rungs)} rungs x 4 primes); "
          f"full columns computed at {len(full_rows)} of them, "
          f"declared a-samples of size {rows[-1]['cells']} at n = 128 "
          f"({len(rows) - len(full_rows)} sample cells)")
    triples_total = sum(r["n"] * (r["n"] - 1) * (r["n"] - 2) // 6
                        for r in full_rows for _ in range(1))
    print(f"distinct triples of mu_n enumerated over the full columns: {triples_total}")
    print("structural checks on every computed cell:")
    bad_total = 0
    for r in rows:
        for a, value in r["counts"].items():
            m = r["n"] // gcd((r["n"] - 1 - a) % r["n"], r["n"])
            if value % m != (1 if r["zeros"][a] else 0):
                bad_total += 1
    print(f"  count congruent to [0 in bad] modulo the orbit modulus m = n/gcd(b-a, n): "
          f"{bad_total} violations over {sum(len(r['counts']) for r in rows)} pencils")
    assert bad_total == 0
    print(f"  count = 1 at a in {{0, 1, n-1}}: "
          f"{sum(1 for r in rows if r['min_at_zero'])}/{len(rows)} cells")
    print(f"  count = n attained exactly at a = 2 (full columns): "
          f"{sum(1 for r in full_rows if r['exact_n'] == [2])}/{len(full_rows)} cells")
    print(f"  column sum over full columns: "
          f"{sum(r['total'] for r in full_rows)}")
    hasher = hashlib.sha256()
    for r in rows:
        hasher.update(f"{r['n']}|{r['tag']}|{r['total']}|{r['digest']}|".encode())
    print(f"  per-cell (n, tag, sum, full-column digest) combined: {hasher.hexdigest()}")
    print("PASS")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
