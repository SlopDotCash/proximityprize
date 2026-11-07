#!/usr/bin/env python3
"""Exact n=128 below-ceiling (t=4) monomial-pencil census at prize scale.

Object.  Fix a prime ``p = 1 (mod n)``, a generator ``g`` of order ``n = 128`` in
``F_p``, the smooth domain ``x_i = g^i``, and the dimension-two code of affine
words ``c0 + c1*x``.  For the monomial pencil ``(u0,u1) = (x^a, x^b)`` the bad
scalars at threshold ``t`` are the gammas for which ``u0 + gamma*u1`` agrees
with an affine word on some set ``S`` with ``|S| >= t`` while ``(u0,u1)`` is not
jointly affine on ``S`` (the ``pairJointAgreesOn`` exclusion of the repository
MCA event).  This probe censuses the below-ceiling threshold ``t = 4`` over all
``n^2 = 16384`` ordered monomial pencils.

Algorithm (shape/orbit, exact integers).  For a triple anchored at ``i`` with
offsets ``(u,v)`` the collinearity determinant factors as
``D_e = V_T * h_{e-2}``, so the bad gamma of a shape is
``-h_{a-2}(1,g^u,g^v) / h_{b-2}(1,g^u,g^v)`` times the phase ``g^{(a-b)i}``.
Scaling the anchor translates the bad gamma by ``g^{b-a}``, so every bad set is
a union of cosets of the subgroup of order ``m = n/gcd((b-a) mod n, n)``, and
the census counts distinct cosets obtained from the ``C(n-1,2)`` triple shapes
and the ``C(n-1,3)`` 4-subset shapes.  The complete homogeneous value comes from
the closed form
``h_k(1,y,z) = ((y-z) + y^{k+2}(z-1) + z^{k+2}(1-y)) / ((1-y)(1-z)(y-z))``.

Exact pruning.  Every legal 4-subset witness contains a legal triple witness
(if all four triples of a witness set were jointly affine, the pair would be
jointly affine on the set), so the t=4 bad set is a subset of the t=3 bad set.
This probe computes a *conservative* t=3 upper bound from distinct anchor
gammas (no coset identification) and runs the 4-subset stage only on pencils
whose upper bound reaches the character-pencil t=4 count.  The t=4 counts are
exact at every pencil that enters that stage; skipped pencils have t=4 strictly
below it.

Reproduced first (published integers, same code path):
  n = 8  (G310/G328): t=4 below-ceiling maximum 9 at (4,3),(4,7),(5,2),(5,6);
  n = 16 (PR #267): character pencils t=4 = 97 at the prize-scale prime;
  n = 32 (PR #272): character pencils t=4 = 897;
  n = 64 (held lane): character pencils t=4 = 7681.

New rung (the claim of this probe).  At ``p = 21*2^128+1`` the four quadratic-
character pencils ``(64,63), (64,127), (65,2), (65,66)`` have

    t=3 count 67585,   t=4 count 63489 = 1 + 128*C(32,2) = 1 + 128*496,

and 63489 is the t=4 maximum over all 16384 monomial pencils, attained exactly
at those four pencils.  The same two integers hold at the further prize-scale
Proth primes ``111*2^128+1`` and ``123*2^128+1`` (character pencils only).
This continues the measured character-pencil rungs
``9 = 1 + 8*C(2,2)``, ``97 = 1 + 16*C(4,2)``, ``897 = 1 + 32*C(8,2)``,
``7681 = 1 + 64*C(16,2)``.

Scope (read before citing).  Finite fields only; the smooth domain ``mu_128``;
dimension-two affine code; monomial pencils only -- this is **not** a maximum
over arbitrary word pairs.  ``n = 128`` is three rungs below the production
``n = 2^30/2^32``; nothing here is a production-regime statement, a ``delta*``
claim, or a step toward the prize.  The ``1 + n*C(n/4,2)`` agreement across five
rungs is an observed pattern in finite data, not a theorem in ``n``.  The
global-max statement is computed by the shape/orbit engine; the independent
crosscheck re-derives the maximizers and a sample directly.  Stdlib only,
deterministic, integer arithmetic only.
"""

import sys
import time
from math import gcd

PRIZE_EXP = 128
PRIZE_K = 21
EXTRA_PRIZE = ((111, 5), (123, 7))

CHAR_T3 = 67585
CHAR_T4 = 63489
N64_T4 = 7681
N32_T4 = 897
N16_T4 = 97
N8_T4 = 9
N8_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))


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


def coset_key(value, m, p):
    """Canonical key of the coset value*H where H has order m in F_p^*."""
    if value == 0:
        return 0
    if m == 1:
        return value
    if m == 2:
        return value * value % p
    return pow(value, m, p)


def char_pencils(n):
    h = n // 2
    return ((h, h - 1), (h, n - 1), (h + 1, 2), (h + 1, h + 2))


def shape_data(n, p):
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
    pair_index = {pair: index for index, pair in enumerate(pairs)}
    denom = [((1 - xs[u]) * (1 - xs[v]) * (xs[u] - xs[v])) % p for u, v in pairs]
    inverse_denom = batch_inverse(denom, p)
    phi = [[0] * len(pairs) for _ in range(n)]
    for slot, (u, v) in enumerate(pairs):
        y, z = xs[u], xs[v]
        inverse = inverse_denom[slot]
        y_power, z_power = 1, 1
        for exponent in range(n):
            numerator = ((y - z) + y_power * (z - 1) + z_power * (1 - y)) % p
            phi[exponent][slot] = numerator * inverse % p
            y_power = y_power * y % p
            z_power = z_power * z % p
    # h_{-2} and h_{-1} vanish; h_0 = 1 at every shape.
    assert not any(phi[0]) and not any(phi[1])
    assert all(value == 1 for value in phi[2])
    quad_shapes = [(pair_index[(u, v)], pair_index[(u, w)])
                   for u in range(1, n)
                   for v in range(u + 1, n)
                   for w in range(v + 1, n)]
    return xs, pairs, phi, quad_shapes


class Census:
    def __init__(self, n, p):
        self.n, self.p = n, p
        self.xs, self.pairs, self.phi, self.quad_shapes = shape_data(n, p)
        self.inverse_phi = [batch_inverse(row, p) for row in self.phi]

    def _ratio(self, a, b):
        p = self.p
        phi_a, phi_b = self.phi[a], self.phi[b]
        inverse_b = self.inverse_phi[b]
        return [
            phi_a[t] * inverse_b[t] % p if phi_b[t] else None
            for t in range(len(self.pairs))
        ]

    def t3_exact(self, a, b):
        """Exact t=3 count (distinct cosets)."""
        p = self.p
        ratio = self._ratio(a, b)
        phi_b = self.phi[b]
        m = self.n // gcd((b - a) % self.n, self.n)
        seen = set()
        add = seen.add
        for slot in range(len(self.pairs)):
            if phi_b[slot]:
                add(coset_key((-ratio[slot]) % p, m, p))
        zero = 0 in seen
        return m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)

    def t3_upper(self, a, b):
        """Conservative t=3 upper bound from distinct anchor gammas."""
        p = self.p
        phi_a, phi_b = self.phi[a], self.phi[b]
        inverse_b = self.inverse_phi[b]
        m = self.n // gcd((b - a) % self.n, self.n)
        seen = set()
        add = seen.add
        for slot in range(len(self.pairs)):
            if phi_b[slot]:
                add((-phi_a[slot] * inverse_b[slot]) % p)
        zero = 0 in seen
        return m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)

    def t4_exact(self, a, b):
        """Exact t=4 count (distinct cosets) via the 4-subset shapes."""
        p = self.p
        phi_a, phi_b = self.phi[a], self.phi[b]
        ratio = self._ratio(a, b)
        m = self.n // gcd((b - a) % self.n, self.n)
        seen = set()
        add = seen.add
        for first_shape, second_shape in self.quad_shapes:
            db_first, db_second = phi_b[first_shape], phi_b[second_shape]
            if db_first:
                if db_second:
                    if ratio[first_shape] == ratio[second_shape]:
                        add(coset_key((-ratio[first_shape]) % p, m, p))
                elif not phi_a[second_shape]:
                    add(coset_key((-ratio[first_shape]) % p, m, p))
            elif db_second and not phi_a[first_shape]:
                add(coset_key((-ratio[second_shape]) % p, m, p))
        zero = 0 in seen
        return m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)


def check_anchors(prize):
    for n, expected, winners_expected in (
        (8, N8_T4, N8_WINNERS),
        (16, N16_T4, char_pencils(16)),
        (32, N32_T4, char_pencils(32)),
        (64, N64_T4, char_pencils(64)),
    ):
        cell = Census(n, prize)
        counts = {}
        for a in range(n):
            for b in range(n):
                counts[(a, b)] = cell.t4_exact(a, b)
        maximum = max(counts.values())
        winners = tuple(sorted(pair for pair, count in counts.items()
                               if count == maximum))
        assert maximum == expected, (n, maximum, expected)
        assert winners == winners_expected, (n, winners, winners_expected)
        print(f"anchor n={n}: t=4 max {maximum} at {winners}", flush=True)
    print("anchors PASS: 9 / 97 / 897 / 7681", flush=True)


def main():
    prize = PRIZE_K * (2 ** PRIZE_EXP) + 1
    assert pow(5, (prize - 1) // 2, prize) == prize - 1
    print(f"n=128 below-ceiling (t=4) census; prize-scale p = {prize}", flush=True)

    t0 = time.time()
    check_anchors(prize)
    print(f"anchor censuses in {time.time() - t0:.1f}s", flush=True)

    cell = Census(128, prize)
    for a, b in char_pencils(128):
        t3 = cell.t3_exact(a, b)
        t4 = cell.t4_exact(a, b)
        assert (t3, t4) == (CHAR_T3, CHAR_T4), (a, b, t3, t4)
        print(f"n=128 character pencil ({a},{b}): t=3 {t3}, t=4 {t4}", flush=True)
    for k, witness in EXTRA_PRIZE:
        p = k * (2 ** PRIZE_EXP) + 1
        assert pow(witness, (p - 1) // 2, p) == p - 1, k
        extra = Census(128, p)
        for a, b in char_pencils(128):
            t3 = extra.t3_exact(a, b)
            t4 = extra.t4_exact(a, b)
            assert (t3, t4) == (CHAR_T3, CHAR_T4), (k, a, b, t3, t4)
        print(f"n=128 character pencils at p = {k}*2^128+1: t=3 {CHAR_T3}, "
              f"t=4 {CHAR_T4}", flush=True)

    print(f"full census at p = {PRIZE_K}*2^128+1 "
          f"(prune by the t=3 upper bound {CHAR_T4})", flush=True)
    t1 = time.time()
    counts = {}
    entered = 0
    for a in range(128):
        for b in range(128):
            if cell.t3_upper(a, b) < CHAR_T4:
                counts[(a, b)] = None
                continue
            entered += 1
            counts[(a, b)] = cell.t4_exact(a, b)
    finite = {pair: count for pair, count in counts.items() if count is not None}
    maximum = max(finite.values())
    winners = tuple(sorted(pair for pair, count in finite.items()
                           if count == maximum))
    print(f"census of 16384 pencils in {time.time() - t1:.1f}s; "
          f"{entered} pencils entered the 4-subset stage", flush=True)
    print(f"t=4 maximum {maximum} at {winners}", flush=True)
    assert maximum == CHAR_T4, maximum
    assert winners == char_pencils(128), winners
    reverse = sorted(finite.items(), key=lambda item: (-item[1], item[0]))
    top = []
    for pair, count in reverse:
        if not top or count != top[-1][1]:
            top.append((pair, count))
        if len(top) == 5:
            break
    print(f"top distinct t=4 values: {[(count, pair) for pair, count in top]}",
          flush=True)
    sample = tuple(sorted({((i * 17) % 128, (i * 29) % 128) for i in range(30)}))
    print("sample " + " ".join(f"{pair}:{counts[pair]}" for pair in sample),
          flush=True)
    assert 2 * maximum <= 128 * 127 * 126 // 6
    print("PASS: exact n=128 t=4 below-ceiling census at the prize-scale prime; "
          "published n=8/16/32/64 anchors reproduced; character pencils reach "
          f"{CHAR_T4} = 1 + 128*C(32,2) and are the unique maximizers",
          flush=True)


if __name__ == "__main__":
    sys.exit(main())
