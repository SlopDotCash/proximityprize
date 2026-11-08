#!/usr/bin/env python3
# Copyright (c) 2026 laooooonn. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
# Authors: laooooonn (GitHub: andyboss1995)
"""Exact ``t = 3`` ceiling census of the column ``b = n - 1`` at NON-two-power rungs.

The campaign's staged column lane measures the column ``b = n - 1`` of the ``t = 3`` ceiling
monomial-pencil census on ``mu_n`` at the two-power rungs ``n = 8..512`` and reports four
structural laws:

* ``L-min``: the column minimum ``1`` is attained exactly at ``a in {0, 1, n-1}``;
* ``L-countn``: the value ``n`` is attained exactly at ``a = 2``;
* ``L-max``: the column maximum is attained exactly at ``a = 6 (mod 8)`` with
  ``a != 30 (mod 32)``;
* ``L-zero``: ``0`` is a bad scalar exactly at ``a = 0 or 1 (mod 4)``.

Those statements are computed for ``n = 2^k`` only.  This probe moves them to the parameter
point the ladder never visits: every ``n`` in ``3..64`` that is NOT a power of two (prime
``n``, ``3 | n``, even-but-not-two-power, odd composites), plus the two-power rungs
``4, 8, 16, 32, 64, 128`` as in-run controls, each over the three smallest primes
``p = 1 (mod n)`` and one Proth-certified large prime ``p = 1 (mod n)``.

Reproduced FIRST, before any new claim:

* the merged ``n = 8`` table: the ``(x^3, x^2)`` ceiling count is ``40`` at every prime
  ``p = 1 (mod 8)`` in ``[17, 20000]`` except ``17`` (``16``) -- all ``556`` primes
  (merged ``scripts/probes/probe_n16_below_ceiling_max.py``);
* the merged ``n = 16`` table: ``464`` at ``245`` of the ``279`` primes ``p = 1 (mod 16)`` in
  ``[17, 20000]``, the other ``34`` exactly the merged exception table;
* the staged two-power column vectors at ``65537`` and at ``21*2^128+1``, matching the vector
  digests of this campaign's UNMERGED staged column lane (attributed as unmerged numbers).

Engine: normalised shapes ``(1, y, z)`` of distinct triples of ``mu_n``, the closed-form row
``h_e``, the dilation orbit modulus ``m = n / gcd(b - a, n)``, coset keying by ``gamma^m``.
Powers are table lookups ``y^e = g^((u*e) mod n)``, not modular exponentiation of ``y``.
Exact integer arithmetic, stdlib only, deterministic; no timing is printed, so the transcript
is byte-reproducible.  Every claim is hard-asserted and exit ``0`` means ``PASS``.

Scope, read before citing.  A finite-field census of one column of one threshold of the
monomial-pencil census on the smooth domain ``mu_n``, at the listed ``n`` and the listed
primes.  Not a theorem in ``n`` or ``p``; not about any other column or row, not about
``t >= 4``, not about global maxima of any census, not about the production regime
``n = 2^30 / 2^32``, not about ``delta*``, not about the prize.  A law failing here is a
computed failure of the COMPUTED statement at that ``n``; no Lean theorem is claimed or
disproved anywhere in this file.
"""

import hashlib
from math import gcd

LIMIT = 20_000
FERMAT = 65537
PRIZE_EXP = 128
PRIZE_K = 21
PROTH_E_MIN = 11
PROTH_E_MAX = 45
PROTH_K_MULT_MAX = 99

N_MIN, N_MAX = 3, 64
CONTROL_EXTRA_RUNGS = (128,)


def sample_a(n):
    """The a-list the second implementation reads at the largest rung (declared, fixed)."""
    return sorted(set(list(range(0, 11))) | {n - 3, n - 2, n - 1})

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
N16_EXCEPTION_COUNT = 34

# Staged, UNMERGED two-power column vectors at b = n - 1: sha256 of the comma-separated
# count list, pinned to this campaign's staged column lane, not to main.
STAGED_TWO_POWER_DIGESTS = {
    (8, "65537"): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, "65537"): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, "65537"): "3cce569863d7fdac3b3c966abcb1c1344bbe0419121e58bdfadb3f0bea11c961",
    (64, "65537"): "69f3e4c5416969ea428cf7fb0e96abd83ba6f6fc3ea11a9932313dfe6d5dfa1c",
    (128, "65537"): "5630704e234513e22d52b9d06f0bb46c3905869e5d675ec99f2194f2be3a8211",
    (8, "21*2^128+1"): "0ddfea9fd767e6bf7711f38258959e41aa5cc352c5dade2e6874f77ca3aaea53",
    (16, "21*2^128+1"): "25b6ea587df4b8b34db831d46b419b5bb7343dca7a50b23df611ae50bc87e316",
    (32, "21*2^128+1"): "a9cce9cbf427e0f50fc3bb15266af206925552ceea154b856f98cc9801b65df5",
    (64, "21*2^128+1"): "e51fbf21f415f7756414d039fca7a9551e045ba468a97e6e928ee2902399594d",
    (128, "21*2^128+1"): "baa6b0809122b4350b40d6482ba73974afe41e24b2d5855ccb55a76c13d8a5fb",
}


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
    if n <= 0:
        return None
    rest = n
    exponent = 0
    while rest % 2 == 0:
        rest //= 2
        exponent += 1
    return exponent if rest == 1 else None


def proth_prime_one_mod(n):
    """Smallest Proth prime k*2^e + 1 == 1 (mod n) with k an odd multiple of the odd part.

    Certified in-run by Proth's theorem: N = k*2^e + 1, k odd, k < 2^e, and a witness a with
    a^((N-1)/2) == -1 (mod N) makes N prime.  Returns (prime, k, e, witness).
    """
    odd = odd_part(n)
    v2 = n // odd
    for e in range(max(PROTH_E_MIN, v2.bit_length() - 1), PROTH_E_MAX + 1):
        for multiple in range(1, PROTH_K_MULT_MAX + 1, 2):
            k = odd * multiple
            if k >= (1 << e):
                break
            if ((k << e) % n):
                continue
            candidate = (k << e) + 1
            for witness in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
                if pow(witness, (candidate - 1) // 2, candidate) == candidate - 1:
                    assert k % 2 == 1 and k < (1 << e)
                    assert (candidate - 1) % n == 0
                    return candidate, k, e, witness
    raise AssertionError(f"no Proth prime found for n={n}")


def prime_factors(value):
    out = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            out.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        out.append(value)
    return out


def order_element(p, n):
    """Element of EXACT order n mod p, verified against every prime divisor of n."""
    if (p - 1) % n:
        raise AssertionError(f"{n} does not divide p-1 for p={p}")
    factors = prime_factors(n)
    candidate = 2
    while candidate < p:
        element = pow(candidate, (p - 1) // n, p)
        if element != 1 and all(pow(element, n // f, p) != 1 for f in factors):
            assert pow(element, n, p) == 1
            return element
        candidate += 1
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
    """Normalised shapes (1, y, z) of distinct triples of mu_n and the closed-form h rows."""

    def __init__(self, n, p):
        self.n, self.p = n, p
        generator = order_element(p, n)
        self.generator = generator
        xs = [pow(generator, exponent, p) for exponent in range(n)]
        assert len(set(xs)) == n and xs[0] == 1
        self.xs = xs
        pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
        self.us = [u for u, v in pairs]
        self.vs = [v for u, v in pairs]
        self.ys = [xs[u] for u in self.us]
        self.zs = [xs[v] for v in self.vs]
        self.diff = [(y - z) % p for y, z in zip(self.ys, self.zs)]
        self.zm1 = [(z - 1) % p for z in self.zs]
        self.ym1 = [(1 - y) % p for y in self.ys]
        denom = [(1 - y) * (1 - z) % p * ((y - z) % p) % p
                 for y, z in zip(self.ys, self.zs)]
        assert all(value for value in denom), "distinct 1, y, z required"
        self.inv_denom = batch_inverse(denom, p)
        assert len(pairs) == (n - 1) * (n - 2) // 2

    def row(self, exponent):
        """h_(exponent-2)(1, y, z) on every shape; powers read from the mu_n table."""
        p, xs, n = self.p, self.xs, self.n
        diff, zm1, ym1, inv = self.diff, self.zm1, self.ym1, self.inv_denom
        us, vs = self.us, self.vs
        return [((diff[i] + xs[(us[i] * exponent) % n] * zm1[i]
                  + xs[(vs[i] * exponent) % n] * ym1[i]) % p) * inv[i] % p
                for i in range(len(us))]

    def count(self, a, b, row_a=None, row_b=None):
        """(count, m, cosets, zero) for the t=3 ceiling event of the pencil (x^a, x^b)."""
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
        total = m * cosets + (1 if zero else 0)
        assert total <= p, (n, p, a, b, total)
        assert cosets <= (p - 1) // m, (n, p, a, b, cosets, m)
        assert m * cosets + (1 if zero else 0) == total
        return total, m, cosets, zero

    def column(self, b):
        row_b = self.row(b)
        counts, profile = {}, {}
        for a in range(self.n):
            total, m, cosets, zero = self.count(a, b, row_b=row_b)
            counts[a] = total
            profile[a] = (m, cosets, zero)
        assert len(counts) == self.n
        return counts, profile


def digest(counts):
    return hashlib.sha256(
        ",".join(str(counts[a]) for a in range(len(counts))).encode()).hexdigest()


def label(p):
    if p == FERMAT:
        return "65537"
    if p == PRIZE_K * (1 << PRIZE_EXP) + 1:
        return f"{PRIZE_K}*2^128+1"
    return str(p)


def fmt_res(modulus, residues):
    """Compact rendering: full residue list when short, otherwise size plus a digest."""
    if modulus is None or residues is None:
        return "d=-[]"
    if len(residues) <= 12:
        return f"d={modulus}[{','.join(str(v) for v in residues)}]"
    short = hashlib.sha256(",".join(str(v) for v in residues).encode()).hexdigest()[:12]
    return f"d={modulus}[{len(residues)}residues:{short}]"


def residue_description(members, n):
    """Smallest modulus d DIVIDING n for which `members` is a union of classes mod d.

    Restricting to d | n keeps the statement inside the natural quotient of Z/n: a condition
    on a mod d with d | n is well defined on the exponent group of mu_n.  Arbitrary moduli
    (e.g. d = 29 at n = 32) are technically satisfiable but number-theoretically vacuous, so
    they are not searched here.  d = n always works, hence the return is never (None, None).
    """
    wanted = tuple(members)
    for d in sorted(divisors(n)):
        residues = frozenset(a % d for a in wanted)
        rebuilt = tuple(a for a in range(n) if a % d in residues)
        if rebuilt == wanted:
            return d, tuple(sorted(residues))
    return None, None


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def cell_laws(n, counts, profile):
    values = [counts[a] for a in range(n)]
    minimum, maximum = min(values), max(values)
    min_set = tuple(a for a in range(n) if counts[a] == minimum)
    countn_set = tuple(a for a in range(n) if counts[a] == n)
    max_set = tuple(a for a in range(n) if counts[a] == maximum)
    zero_set = tuple(a for a in range(n) if profile[a][2])
    expected_min = tuple(sorted({0, 1, n - 1}))
    expected_max = tuple(a for a in range(n) if a % 8 == 6 and a % 32 != 30)
    expected_zero = tuple(a for a in range(n) if a % 4 in (0, 1))
    zero_mod, zero_res = residue_description(zero_set, n)
    max_mod, max_res = residue_description(max_set, n)
    return {
        "min": minimum, "max": maximum, "sum": sum(values), "digest": digest(counts),
        "min_set": min_set, "countn_set": countn_set, "max_set": max_set,
        "zero_set": zero_set,
        "zero_mod": zero_mod, "zero_res": zero_res,
        "max_mod": max_mod, "max_res": max_res,
        "L_min": min_set == expected_min and minimum == 1,
        "L_countn": countn_set == (2,),
        "L_max": max_set == expected_max,
        "L_zero": zero_set == expected_zero,
        "vacuous_max": not expected_max,
        "vacuous_zero": not expected_zero,
    }


def main():
    print("t=3 ceiling census of the column b = n-1 at non-two-power rungs")
    print(f"parameters: n in [{N_MIN},{N_MAX}] plus controls {CONTROL_EXTRA_RUNGS}; "
          f"sieve limit {LIMIT}; regimes = 3 smallest p=1 (mod n) + one Proth prime")
    prize = PRIZE_K * (1 << PRIZE_EXP) + 1

    # ---- 1. merged anchors recomputed with this engine ------------------------------
    table8 = {p: Shapes(8, p).count(3, 2)[0] for p in primes_one_mod(8)}
    assert len(table8) == N8_PRIME_COUNT, len(table8)
    for p, value in table8.items():
        assert value == N8_CEILING_EXCEPTIONS.get(p, N8_CEILING_DEFAULT), (p, value)
    print(f"anchor n=8: {len(table8)} primes p=1 (mod 8) in [17,{LIMIT}]; "
          f"ceiling {N8_CEILING_DEFAULT} at {len(table8) - 1} of them, "
          f"{N8_CEILING_EXCEPTIONS} -- merged table reproduced entry by entry")

    table16 = {p: Shapes(16, p).count(3, 2)[0] for p in primes_one_mod(16)}
    assert len(table16) == N16_PRIME_COUNT, len(table16)
    for p, value in table16.items():
        assert value == N16_CEILING_EXCEPTIONS.get(p, N16_CEILING_DEFAULT), (p, value)
    exceptions_hit = sorted(p for p in table16 if p in N16_CEILING_EXCEPTIONS)
    assert len(exceptions_hit) == N16_EXCEPTION_COUNT
    assert exceptions_hit == sorted(N16_CEILING_EXCEPTIONS)
    print(f"anchor n=16: {len(table16)} primes, {N16_CEILING_DEFAULT} at "
          f"{len(table16) - N16_EXCEPTION_COUNT}, merged {N16_EXCEPTION_COUNT}-prime "
          f"exception set matched exactly")

    # ---- 2. staged two-power columns (campaign's own UNMERGED digests) --------------
    for p, tag in ((FERMAT, "65537"), (prize, f"{PRIZE_K}*2^128+1")):
        for n in (8, 16, 32, 64, 128):
            counts, _ = Shapes(n, p).column(n - 1)
            assert digest(counts) == STAGED_TWO_POWER_DIGESTS[(n, tag)], (n, tag)
        print(f"staged control columns at {tag}: n=8,16,32,64,128 vectors match the "
              f"campaign's unmerged staged digests")

    # ---- 3. the new parameter point --------------------------------------------------
    rungs = list(range(N_MIN, N_MAX + 1)) + list(CONTROL_EXTRA_RUNGS)
    cells = []
    for n in rungs:
        small = primes_one_mod(n, 3)
        assert len(small) == 3, (n, small)
        large, k_proth, e_proth, witness = proth_prime_one_mod(n)
        for p in small + [large]:
            shapes = Shapes(n, p)
            counts, profile = shapes.column(n - 1)
            info = cell_laws(n, counts, profile)
            info["counts"] = counts
            info["n"] = n
            info["prime"] = p
            info["tag"] = label(p)
            info["family"] = "control-2^k" if two_power_exponent(n) is not None else "new"
            info["is_proth"] = (p == large)
            info["proth"] = (k_proth, e_proth, witness)
            cells.append(info)

    print()
    print(f"grid cells: {len(cells)} = {len(rungs)} rungs x 4 primes; "
          f"new (non-two-power) {sum(1 for c in cells if c['family'] == 'new')}, "
          f"controls {sum(1 for c in cells if c['family'] != 'new')}")
    print("Proth primes: certified in-run (k odd, k < 2^e, witness a^((N-1)/2) = -1) for "
          "every rung; smallest and largest used:")
    proth_cells = [c for c in cells if c["is_proth"]]
    smallest = min(proth_cells, key=lambda c: c["prime"])
    largest = max(proth_cells, key=lambda c: c["prime"])
    print(f"  smallest {smallest['prime']} = {smallest['proth'][0]}*2^"
          f"{smallest['proth'][1]}+1 at n={smallest['n']} "
          f"(witness {smallest['proth'][2]})")
    print(f"  largest  {largest['prime']} = {largest['proth'][0]}*2^"
          f"{largest['proth'][1]}+1 at n={largest['n']} (witness {largest['proth'][2]})")

    groups = {"control-2^k": [c for c in cells if c["family"] == "control-2^k"],
              "new n>=8": [c for c in cells if c["family"] == "new" and c["n"] >= 8],
              "new n<8": [c for c in cells if c["family"] == "new" and c["n"] < 8]}
    print()
    print("law status by rung family (cells where the law holds / cells):")
    for name, rows in groups.items():
        line = [f"{name:13s}"]
        for law in ("L_min", "L_countn", "L_max", "L_zero"):
            holds = sum(1 for c in rows if c[law])
            line.append(f"{law}={holds}/{len(rows)}")
        vacuous = sum(1 for c in rows if c["vacuous_max"])
        line.append(f"(L-max description empty at {vacuous} cells)")
        print("  " + "  ".join(line))

    print()
    print("per-law failure inventory at new (non-two-power) rungs with n >= 8:")
    for law in ("L_min", "L_countn", "L_max", "L_zero"):
        fails = [c for c in groups["new n>=8"] if not c[law]]
        rungs_failed = sorted({c["n"] for c in fails})
        always = [c for c in fails if all(not x[law] for x in groups["new n>=8"]
                                          if x["n"] == c["n"])]
        print(f"  {law}: {len(fails)}/{len(groups['new n>=8'])} cells fail; "
              f"failing rungs {rungs_failed[:14]}"
              f"{' ...' if len(rungs_failed) > 14 else ''}")
        for cell in fails[:3]:
            which = (cell["min_set"] if law == "L_min" else
                     cell["countn_set"] if law == "L_countn" else
                     cell["max_set"] if law == "L_max" else cell["zero_set"])
            shown = which if len(which) <= 12 else f"{which[:12]}...({len(which)})"
            print(f"    n={cell['n']} p={cell['tag']}: actual set {shown}")
        if always:
            print(f"    rungs where the law fails at ALL four of its primes: "
                  f"{sorted({c['n'] for c in always})[:14]}")

    print()
    print("rungs at which every one of the four laws holds at every prime (new family):")
    clean = []
    for n in sorted({c["n"] for c in groups["new n>=8"]}):
        rows = [c for c in groups["new n>=8"] if c["n"] == n]
        if all(c["L_min"] and c["L_countn"] and c["L_max"] and c["L_zero"] for c in rows):
            clean.append(n)
    new_rungs = sorted({c["n"] for c in groups["new n>=8"]})
    print(f"  {clean if clean else 'NONE'}  "
          f"({len(clean)} of {len(new_rungs)} new rungs with n >= 8)")

    print()
    print("residue descriptions over divisor moduli of n (d | n, smallest such d):")
    for key, mod_key, res_key in (("zero-membership", "zero_mod", "zero_res"),
                                  ("column maximum", "max_mod", "max_res")):
        proper = [c for c in cells if c[mod_key] < c["n"]]
        binary = [c for c in cells if c[res_key] == (0, 1)]
        print(f"  {key}: proper divisor modulus (d < n) at {len(proper)}/{len(cells)} cells; "
              f"residue set exactly {{0,1}} at {len(binary)}/{len(cells)} cells")
        for family in ("control-2^k", "new"):
            rows = [c for c in cells if c["family"] == family]
            mods = sorted({c[mod_key] for c in rows})
            d4 = sum(1 for c in rows if c[mod_key] == 4)
            bin_fam = sum(1 for c in rows if c[res_key] == (0, 1))
            print(f"    {family:12s}: {len(rows)} cells, minimal d in {mods[:14]}"
                  f"{'...' if len(mods) > 14 else ''}, d=4 at {d4}, "
                  f"residues {{0,1}} at {bin_fam}")
        prime_independent = 0
        rung_list = sorted({c["n"] for c in cells})
        for n in rung_list:
            rows = [c for c in cells if c["n"] == n]
            if len({(c[mod_key], c[res_key]) for c in rows}) == 1:
                prime_independent += 1
        print(f"    rungs whose {key} description is identical at all four primes: "
              f"{prime_independent}/{len(rung_list)}")

    print()
    print("zero-membership as a {0,1}-residue law, rung by rung (d, R) per prime:")
    for n in sorted({c["n"] for c in cells}):
        rows = [c for c in cells if c["n"] == n]
        if all(c["zero_res"] == (0, 1) for c in rows):
            print(f"  n={n:4d} {rows[0]['family']:12s} d={rows[0]['zero_mod']} at all "
                  f"{len(rows)} primes -- law holds with the modulus moved from 4 to d")

    print()
    print("two-power controls: does the published mod-4 zero law reappear at small primes?")
    for n in sorted({c["n"] for c in groups["control-2^k"]}):
        rows = [c for c in groups["control-2^k"] if c["n"] == n]
        parts = []
        for c in rows:
            parts.append(f"{c['tag']}:z{len(c['zero_set'])},{fmt_res(c['zero_mod'], c['zero_res'])}")
        print(f"  n={n:4d} " + "  ".join(parts))

    print()
    print("per-cell records (one line per (n, p) cell; digest is the first 16 hex of the "
          "sha256 of the comma-separated count vector in a = 0..n-1 order; the full-vector "
          "combined digest is printed at the end):")
    for c in cells:
        print(f"CELL n={c['n']} p={c['tag']} sum={c['sum']} max={c['max']} "
              f"zero={len(c['zero_set'])} exactn={len(c['countn_set'])} "
              f"digest={c['digest'][:16]}")

    print()
    print("sample cells (the largest rung, where the second implementation reads a declared "
          "a-list rather than the whole column):")
    for c in cells:
        if c["n"] in CONTROL_EXTRA_RUNGS:
            pairs = ";".join(f"{a}:{c['counts'][a]}" for a in sample_a(c["n"]))
            print(f"SAMPLE n={c['n']} p={c['tag']} pairs={pairs}")

    print()
    print("per-rung summary: 4 cells as tag:max/zero-set description/vector digest/"
          "flags(L_min,L_countn,L_max,L_zero)")
    for n in sorted({c["n"] for c in cells}):
        rows = [c for c in cells if c["n"] == n]
        parts = []
        for c in rows:
            flags = "".join("1" if c[law] else "0"
                            for law in ("L_min", "L_countn", "L_max", "L_zero"))
            zero_part = f"z{len(c['zero_set'])}," \
                        f"{fmt_res(c['zero_mod'], c['zero_res'])}"
            parts.append(f"{c['tag']}:max{c['max']}/{zero_part}/"
                         f"{c['digest'][:10]}/{flags}")
        print(f"  n={n:4d} {rows[0]['family']:12s} " + "  ".join(parts))

    print()
    hasher = hashlib.sha256()
    for c in cells:
        hasher.update(f"{c['n']}|{c['tag']}|{c['digest']}|".encode())
    print(f"grid cell count: {len(cells)}")
    print(f"full count-vector digests combined over the grid, in rung-then-prime order: "
          f"{hasher.hexdigest()}")
    print("distinct column vectors across the grid: "
          f"{len({c['digest'] for c in cells})}")
    print("PASS")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()
