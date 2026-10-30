#!/usr/bin/env python3
"""Independent re-computation of the n=64 below-ceiling monomial-pencil census.

This file deliberately does not share code with
``probe_n64_below_ceiling_max.py``.  It re-derives the same finite-field
integers through three separate devices:

1. A *literal* MCA event at ``n = 8``: for every scalar ``gamma`` in ``F_p``,
   every pencil and every 3- or 4-subset, decide collinearity by the secant
   slope test ``(x_b - x_a)(f_c - f_a) = (x_c - x_a)(f_b - f_a)``, and check the
   ``pairJointAgreesOn`` exclusion directly.  No determinants, no divided
   differences.  This pins the semantics of the event itself.

2. A shape/orbit algorithm.  For a triple anchored at ``i`` with offsets
   ``(u,v)`` the collinearity determinant factors as
   ``D_e = V_T * h_{e-2}``, so the gamma ratio ``-D_a/D_b`` equals
   ``-h_{a-2}(u,v)/h_{b-2}(u,v)`` -- a function of the *shape* alone times the
   phase ``g^((a-b)i)``.  The complete homogeneous value is computed from the
   closed form

       h_k(1,y,z) = (y-z) + y^(k+2)(z-1) + z^(k+2)(1-y)  /  ((1-y)(1-z)(y-z))

   with ``y = g^u``, ``z = g^v``.  Consequently every bad scalar of the pencil
   ``(a,b)`` lies in a full translation coset of the subgroup of order
   ``m = n/gcd(b-a,n)``, and the census is a count of distinct cosets.  This
   algorithm never enumerates 4-subsets: it enumerates the ``C(n-1,3)``
   *shapes* and counts cosets.

3. Full-census checksums at ``n = 64`` (sum of all 4096 counts and the
   position-weighted sum) that must equal the numbers printed by the direct
   determinant probe, so agreement covers every pencil, not just the maximum.

Reproduced anchors (published integers): n=8 G310/G328 (16/40 and 9 at
(4,3),(4,7),(5,2),(5,6)), n=16 PR #267 spots (incl. 353 -> 81), n=32 PR #272
(4640 ceiling max, 897 below max), and the held n=64 t=3 maxima.

Scope: same as the main probe -- finite fields, fixed rungs, monomial pencils
only, no production statement, no delta* claim.
"""

from itertools import combinations
from math import gcd

G328_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))
N16_FOUR = ((8, 7), (8, 15), (9, 2), (9, 10))
PRIZE_EXP = 128
PRIZE_K = 21

# n=64 t=4 cells asserted by the main probe.
N64_T4 = {
    12289: (6081, ((32, 63), (33, 2))),
    65537: (6721, ((32, 31), (33, 34))),
}
N64_T4_PRIZE = (7681, ((32, 31), (32, 63), (33, 2), (33, 34)))

# (sum of the 4096 below-ceiling counts, position-weighted sum) printed by the
# direct determinant probe; see the PR body.
N64_T4_CHECKSUMS = {
    12289: (1102306, 2328367473),
    65537: (1006946, 2126919473),
    7145929705339707732730866756067132440577: (1008370, 2129927673),
}


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


def shape_data(n, p):
    """Pair shapes, complete homogeneous values, and the coset table."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    pairs = [(u, v) for u in range(1, n) for v in range(u + 1, n)]
    pair_index = {pair: index for index, pair in enumerate(pairs)}
    denom = []
    for u, v in pairs:
        y, z = xs[u], xs[v]
        denom.append(((1 - y) * (1 - z) * (y - z)) % p)
    inverse_denom = batch_inverse(denom, p)
    phi = [[0] * len(pairs) for _ in range(n)]
    for slot, (u, v) in enumerate(pairs):
        y, z = xs[u], xs[v]
        inverse = inverse_denom[slot]
        y_power, z_power = 1, 1
        for exponent in range(n):
            # h_{exponent-2}(1,y,z) with the closed form above.
            numerator = ((y - z) + y_power * (z - 1) + z_power * (1 - y)) % p
            phi[exponent][slot] = numerator * inverse % p
            y_power = y_power * y % p
            z_power = z_power * z % p
    # h_{-2} and h_{-1} vanish; h_0 = 1 at every shape.  Exact identities.
    assert not any(phi[0]) and not any(phi[1]), "closed form: h_{-2}, h_{-1} = 0"
    assert all(value == 1 for value in phi[2]), "closed form: h_0 = 1"
    return xs, pairs, pair_index, phi


CENSUS_CACHE = {}


def coset_counts(n, p):
    """Full census through shapes and translation cosets (no 4-subset loop)."""
    if (n, p) in CENSUS_CACHE:
        return CENSUS_CACHE[(n, p)]
    xs, pairs, pair_index, phi = shape_data(n, p)
    inverse_phi = [batch_inverse(row, p) for row in phi]
    quad_shapes = [(pair_index[(u, v)], pair_index[(u, w)])
                   for u in range(1, n)
                   for v in range(u + 1, n)
                   for w in range(v + 1, n)]
    counts_ceiling = {}
    counts_below = {}
    for a in range(n):
        phi_a = phi[a]
        inverse_a = inverse_phi[a]
        for b in range(n):
            if b < 2:
                # u1 affine on every witness: the pair-joint exclusion fires.
                # a < 2 with b >= 2 falls through and counts {0} exactly.
                counts_ceiling[(a, b)] = 0
                counts_below[(a, b)] = 0
                continue
            phi_b = phi[b]
            inverse_b = inverse_phi[b]
            ratio = [phi_a[t] * inverse_b[t] % p for t in range(len(pairs))]
            m = n // gcd((b - a) % n, n)
            # t = 3: every pair shape with D_b != 0 contributes one gamma.
            seen = set()
            add = seen.add
            for slot in range(len(pairs)):
                if phi_b[slot]:
                    add(coset_key((-ratio[slot]) % p, m, p))
            zero = 0 in seen
            counts_ceiling[(a, b)] = m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)
            seen = set()
            add = seen.add
            for first_shape, second_shape in quad_shapes:
                db_first = phi_b[first_shape]
                db_second = phi_b[second_shape]
                if db_first:
                    if db_second:
                        if ratio[first_shape] == ratio[second_shape]:
                            add(coset_key((-ratio[first_shape]) % p, m, p))
                    elif not phi_a[second_shape]:
                        add(coset_key((-ratio[first_shape]) % p, m, p))
                elif db_second and not phi_a[first_shape]:
                    add(coset_key((-ratio[second_shape]) % p, m, p))
            zero = 0 in seen
            counts_below[(a, b)] = m * (len(seen) - (1 if zero else 0)) + (1 if zero else 0)
    CENSUS_CACHE[(n, p)] = (counts_ceiling, counts_below)
    return counts_ceiling, counts_below


def checksum(counts, n):
    total = sum(counts.values())
    weighted = sum(count * (a * n + b) for (a, b), count in counts.items())
    return total, weighted


def summarize(counts):
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items()
                           if count == maximum))
    return maximum, winners


def collinear(xs, values, subset, p):
    i, j = subset[0], subset[1]
    dx = (xs[j] - xs[i]) % p
    dy = (values[j] - values[i]) % p
    for other in subset[2:]:
        if ((xs[other] - xs[i]) * dy - (values[other] - values[i]) * dx) % p:
            return False
    return True


def literal_bad_set(n, p, a, b, size):
    """Direct event: every gamma, every `size`-subset, secant-slope test."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    u0 = [pow(x, a, p) for x in xs]
    u1 = [pow(x, b, p) for x in xs]
    subsets = list(combinations(range(n), size))
    bad = set()
    for gamma in range(p):
        values = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
        for subset in subsets:
            if collinear(xs, values, subset, p):
                if not (collinear(xs, u0, subset, p)
                        and collinear(xs, u1, subset, p)):
                    bad.add(gamma)
                    break
    return bad


def main():
    print("independent re-computation of the n=64 below-ceiling census")
    print("algorithm: literal secant events (n=8), shape/closed-form coset counts")

    # 1. Literal event at n=8, all 64 pencils, all scalars, both thresholds.
    for p in (17, 41, 257):
        ceiling_max = 0
        below_max = 0
        below_winners = []
        for a in range(8):
            for b in range(8):
                ceiling = len(literal_bad_set(8, p, a, b, 3))
                below = len(literal_bad_set(8, p, a, b, 4))
                if (a, b) == (3, 2):
                    assert ceiling == (16 if p == 17 else 40), (p, ceiling)
                ceiling_max = max(ceiling_max, ceiling)
                if below > below_max:
                    below_max = below
                    below_winners = [(a, b)]
                elif below == below_max and below:
                    below_winners.append((a, b))
        assert below_max == 9, (p, below_max)
        assert tuple(sorted(below_winners)) == tuple(sorted(G328_WINNERS)), (
            p, below_winners)
        counts_ceiling, counts_below = coset_counts(8, p)
        assert summarize(counts_below) == (9, G328_WINNERS), (p,)
        assert summarize(counts_ceiling)[0] == ceiling_max, (p,)
        print(f"n=8 p={p}: literal t=3 (3,2) "
              f"{16 if p == 17 else 40}, literal t=4 max 9 at {G328_WINNERS}; "
              "shape census agrees on all 64 pencils")

    # 2. Shape census at the published n=16 and n=32 anchors.
    for p, expected_stack, expected_max, expected_winners in (
        (17, 17, 17, None),
        (353, 272, 81, N16_FOUR),
        (65537, 464, 97, N16_FOUR),
    ):
        counts_ceiling, counts_below = coset_counts(16, p)
        assert counts_ceiling[(3, 2)] == expected_stack, (p, counts_ceiling[(3, 2)])
        maximum, winners = summarize(counts_below)
        assert maximum == expected_max, (p, maximum)
        if expected_winners is not None:
            assert winners == expected_winners, (p, winners)
    print("n=16 shape census: 17 -> 17, 353 -> 81, 65537 -> 97 at the four "
          "char pencils (published PR #267 integers)")

    prize = PRIZE_K * (2 ** PRIZE_EXP) + 1
    assert pow(5, (prize - 1) // 2, prize) == prize - 1
    for p, expected_stack in ((65537, 3264), (prize, 4512)):
        counts_ceiling, counts_below = coset_counts(32, p)
        assert counts_ceiling[(3, 2)] == expected_stack, (p,)
        assert summarize(counts_ceiling)[0] == 4640, (p,)
        assert summarize(counts_below) == (
            897, ((16, 31), (17, 2)) if p == 65537
            else ((16, 15), (16, 31), (17, 2), (17, 18))), (p,)
    print("n=32 shape census: (3,2) 3264/4512, t=3 max 4640, t=4 max 897 "
          "(published PR #272 integers)")

    # 3. n=64 t=3 held-lane anchors through this third algorithm.
    held = {
        12289: (12160, 12161, None),
        65537: (13761, 31744, ((11, 18), (18, 11), (47, 54), (54, 47))),
        prize: (39744, 40512, None),
    }
    for p, (stack, top, winners_expected) in held.items():
        counts_ceiling, _ = coset_counts(64, p)
        assert counts_ceiling[(3, 2)] == stack, (p, counts_ceiling[(3, 2)])
        top_value, winners = summarize(counts_ceiling)
        assert top_value == top, (p, top_value)
        if winners_expected is not None:
            assert winners == winners_expected, (p, winners)
    assert len(summarize(coset_counts(64, prize)[0])[1]) == 224
    print("n=64 t=3 held-lane anchors reproduced: (3,2) 12160/13761/39744, "
          "max 12161/31744/40512, 224 prize-scale maximizers")

    # 4. Full n=64 t=4 censuses.  Every one of the 4096 counts must match the
    #    direct determinant probe through the checksums.
    cells = [(12289, N64_T4[12289]), (65537, N64_T4[65537]),
             (prize, N64_T4_PRIZE)]
    for p, (expected_max, expected_winners) in cells:
        _, counts_below = coset_counts(64, p)
        maximum, winners = summarize(counts_below)
        assert maximum == expected_max, (p, maximum, expected_max)
        assert 2 * maximum <= 64 * 63 * 62 // 6, (p, maximum)
        assert winners == expected_winners, (p, winners)
        total, weighted = checksum(counts_below, 64)
        print(f"n=64 p={p}: t=4 max {maximum} at {winners}; checksum "
              f"sum {total} / weighted {weighted}")
        if p in N64_T4_CHECKSUMS:
            assert (total, weighted) == N64_T4_CHECKSUMS[p], (p, total, weighted)
    print("PASS: literal n=8 events, the shape/orbit census and the direct "
          "determinant census agree on every asserted integer")


if __name__ == "__main__":
    main()
