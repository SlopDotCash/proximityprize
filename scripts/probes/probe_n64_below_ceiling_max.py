#!/usr/bin/env python3
"""Exact n=64 dimension-two below-ceiling monomial-pencil census.

Object.  Fix a prime ``p = 1 (mod 64)``, a generator ``g`` of order ``n = 64`` in
``F_p``, the smooth domain ``x_i = g^i``, and the dimension-two code of affine
words ``c0 + c1*x``.  For the monomial pencil ``(u0,u1) = (x^a, x^b)`` the
*bad* scalars are the gammas for which ``u0 + gamma*u1`` agrees with an affine
word on some set ``S`` with ``|S| >= t`` while ``(u0,u1)`` is not jointly affine
on ``S`` (the ``pairJointAgreesOn`` exclusion of the repository MCA event).
This probe censuses two thresholds:

  t = 3 (``ceiling``): every triple is a legal witness;
  t = 4 (``below-ceiling``): only 4-subsets are.

Algorithm (exact, integer, no floating point).  Write ``D_e(T)`` for the 2x2
collinearity determinant of ``(x_i, x_i^e)`` on the triple ``T = (i,j,k)``.
Since ``D_e = V_T * h_{e-2}(x_i,x_j,x_k)`` (``V_T`` the Vandermonde product,
``h`` the complete homogeneous polynomial), the triple condition is linear in
gamma and the t = 3 bad set is exactly

    { -D_a(T)/D_b(T) : T a triple with D_b(T) != 0 }.

For t = 4 the same linearity holds on every triple of a 4-subset ``S``; the
four points of ``S`` are collinear for gamma iff two triples of ``S`` that share
two points both vanish at gamma, so

    gamma is bad  <=>  some 4-subset (i,j,k,l) has
                       D_a(i,j,k) + gamma*D_b(i,j,k) = 0  and
                       D_a(i,j,l) + gamma*D_b(i,j,l) = 0,

with the usual degenerate conventions when ``D_b`` vanishes on one of the two
triples (then ``D_a`` must vanish there).  Both conditions are exact iff
characterisations: a witness set on which ``u1`` were affine would make
``u0 = (u0 + gamma*u1) - gamma*u1`` affine too, contradicting the exclusion, so
the witness always contains a triple with ``D_b != 0``.

Affine rows.  For ``b < 2`` the second word is affine on every witness, so the
pair-joint exclusion fires for every gamma and the bad set is empty.  For
``a < 2`` with ``b >= 2`` the condition is exact and gives exactly ``{0}``:
``gamma = 0`` is bad with the whole domain as witness, because ``u0`` is a
codeword while ``x^b`` is not affine on the whole domain.  No other ``gamma``
survives: if ``u0 + gamma*u1`` were affine on a witness, then so would be
``u1 = ((u0 + gamma*u1) - u0)/gamma``, and the pair-joint exclusion would fire.

Reproduced first (published integers, same code path):
  n = 8  (G310/G328): (3,2) t=3 count 16 at p=17 and 40 at p=41,257; t=4
         below-ceiling maximum 9 at (4,3),(4,7),(5,2),(5,6);
  n = 16: 14 published spot primes (incl. the 353 exception, 81) and the
         prize-scale maximum 97 at (8,7),(8,15),(9,2),(9,10);
  n = 32 (PR #272): t=3 (3,2) count 3264 at p=65537 / 4512 at prize scale,
         t=3 maximum 4640, t=4 below-ceiling maximum 897;
  n = 64 t=3 (held lane, reproduced through this code path): maximum 31744 at
         p=65537 and 40512 at the prize-scale prime.

New rung (the claim of this probe).  Full census over all 4096 ordered
monomial pencils at three primes ``p = 1 (mod 64)``: the t = 4 below-ceiling
maximum is

  6081 at p = 12289, attained at (32,63) and (33,2);
  6721 at p = 65537,  attained at (32,31) and (33,34);
  7681 at the prize-scale prime p = 21*2^128 + 1, attained at the four
  quadratic-character pencils (32,31),(32,63),(33,2),(33,34).

At prize scale ``7681 = 1 + 64*C(16,2)``, continuing the published rungs
``9 = 1 + 8*C(2,2)`` (n=8), ``97 = 1 + 16*C(4,2)`` (n=16) and
``897 = 1 + 32*C(8,2)`` (n=32) on the measured maximizers.  Field dependence is
measured, not assumed: the maximum drops to 6721 and 6081 at the smaller primes
and the maximiser sets move.

Scope (read before citing).  Finite fields only; fixed rungs n in
{8,16,32,64}; monomial pencils only -- this is **not** a maximum over
arbitrary word pairs, and the ``#bad * 2 <= C(n,3)`` good-side bound is far
above the census value.  ``n = 64`` is four rungs below the production
``n = 2^30/2^32``; nothing here is a production-regime statement, a ``delta*``
claim, or a step toward the prize.  The ``1 + n*C(n/4,2)`` agreement across
four rungs is an observed pattern in finite data, not a theorem in ``n``.
Stdlib only, deterministic, integer arithmetic only.
"""

from itertools import combinations

T_CEIL = 3
T_BELOW = 4
PRIZE_EXP = 128
PRIZE_K = 21

G328_WINNERS = ((4, 3), (4, 7), (5, 2), (5, 6))
N16_FOUR = ((8, 7), (8, 15), (9, 2), (9, 10))

# Published n=16 spot values (PR #267 / probe_n16_below_ceiling_max.py):
# p -> (t=3 (3,2) count, t=4 below-ceiling maximum, maximizers).
N16_SPOT = {
    17: (17, 17, None),
    97: (96, 97, ((8, 15), (9, 2))),
    113: (112, 97, ((8, 7), (9, 10))),
    193: (192, 97, N16_FOUR),
    241: (240, 97, ((8, 15), (9, 2))),
    257: (224, 97, ((8, 15), (9, 2))),
    337: (272, 97, N16_FOUR),
    353: (272, 81, N16_FOUR),
    449: (336, 97, ((8, 15), (9, 2))),
    1201: (464, 97, N16_FOUR),
    1217: (448, 97, ((8, 15), (9, 2))),
    12289: (464, 97, N16_FOUR),
    19489: (464, 97, N16_FOUR),
    65537: (464, 97, N16_FOUR),
}

N32_T3_MAX = 4640
N32_T3_WINNERS_65537 = ((3, 26), (7, 30), (26, 3), (30, 7))
N32_T4_MAX = 897
N32_T4_WINNERS_65537 = ((16, 31), (17, 2))

N64_T3_MAX_12289 = 12161
N64_T3_MAX_65537 = 31744
N64_T3_WINNERS_65537 = ((11, 18), (18, 11), (47, 54), (54, 47))
N64_T3_MAX_PRIZE = 40512
N64_T3_PRIZE_WINNER_COUNT = 224
N64_T3_PRIZE_SAMPLE = ((2, 11), (2, 19), (2, 27), (2, 43),
                       (2, 51), (2, 59), (3, 6), (3, 18))

# n=64 t=4 below-ceiling cells (the new claim).
N64_T4 = {
    12289: (6081, ((32, 63), (33, 2))),
    65537: (6721, ((32, 31), (33, 34))),
}

# Full-census checksums (sum of all 4096 counts, position-weighted sum), so
# that the independent implementation can assert agreement on every pencil.
N64_T4_CHECKSUMS = {
    12289: (1102306, 2328367473),
    65537: (1006946, 2126919473),
}
N64_T4_PRIZE_CHECKSUM = (1008370, 2129927673)


def char_pencils(n):
    """The four quadratic-character pencils (x^h,.) with h = n/2, odd gap."""
    h = n // 2
    return ((h, h - 1), (h, n - 1), (h + 1, 2), (h + 1, h + 2))


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
    """Invert a list mod p in O(len) multiplications; zeros map to zero."""
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


def build_cell(n, p):
    """Domain, collinearity determinants on every triple, and quad pairs."""
    generator = order_element(p, n)
    xs = [pow(generator, exponent, p) for exponent in range(n)]
    assert len(set(xs)) == n
    triples = list(combinations(range(n), 3))
    triple_index = {triple: index for index, triple in enumerate(triples)}
    determinants = []
    for exponent in range(n):
        word = [pow(x, exponent, p) for x in xs]
        determinants.append([
            ((xs[j] - xs[i]) * (word[k] - word[i])
             - (xs[k] - xs[i]) * (word[j] - word[i])) % p
            for i, j, k in triples
        ])
    quads = [(triple_index[(i, j, k)], triple_index[(i, j, l)])
             for i, j, k, l in combinations(range(n), 4)]
    return xs, determinants, quads, triples


def bad_sets(determinants, second_inverse, quads, triples, a, b, p):
    """Exact t=3 ceiling set and t=4 below-ceiling set of the pencil (a,b)."""
    if b < 2:
        # x^1 is affine on every witness, so any witness for u0 + gamma*u1 is
        # also one for u0 and the pair-joint exclusion always fires.  For
        # a < 2 and b >= 2 the general path below is exact and returns {0}:
        # gamma = 0 is bad with the whole domain as witness, since u0 is a
        # codeword but u1 = x^b is not affine on the whole domain.
        return set(), set()
    first = determinants[a]
    second = determinants[b]
    ratio = [(first[t] * second_inverse[t]) % p if second[t] else None
             for t in range(len(second))]
    ceiling = set()
    add_ceiling = ceiling.add
    for value in ratio:
        if value is not None:
            add_ceiling((-value) % p)
    below = set()
    add_below = below.add
    for base, fourth in quads:
        rb = ratio[base]
        if rb is not None:
            rf = ratio[fourth]
            if rf is None:
                if first[fourth] == 0:
                    add_below((-rb) % p)
            elif rb == rf:
                add_below((-rb) % p)
        else:
            rf = ratio[fourth]
            if rf is not None and first[base] == 0:
                add_below((-rf) % p)
    return ceiling, below


CENSUS_CACHE = {}


def census(n, p):
    """Full monomial-pencil census at one prime; returns both profiles."""
    if (n, p) in CENSUS_CACHE:
        return CENSUS_CACHE[(n, p)]
    xs, determinants, quads, triples = build_cell(n, p)
    inverse_cache = {}
    counts_ceiling = {}
    counts_below = {}
    for b in range(n):
        if b < 2:
            continue
        inverse_cache[b] = batch_inverse(determinants[b], p)
    for a in range(n):
        for b in range(n):
            ceiling, below = bad_sets(
                determinants, inverse_cache.get(b, []), quads, triples, a, b, p
            )
            counts_ceiling[(a, b)] = len(ceiling)
            counts_below[(a, b)] = len(below)
    CENSUS_CACHE[(n, p)] = (xs, counts_ceiling, counts_below)
    return xs, counts_ceiling, counts_below


def summarize(counts):
    maximum = max(counts.values())
    winners = tuple(sorted(pair for pair, count in counts.items()
                           if count == maximum))
    return maximum, winners


def checksum(counts, n):
    total = sum(counts.values())
    weighted = sum(count * (a * n + b) for (a, b), count in counts.items())
    return total, weighted


def prize_prime():
    p = PRIZE_K * (2 ** PRIZE_EXP) + 1
    assert PRIZE_K % 2 == 1 and PRIZE_K < 2 ** PRIZE_EXP
    # Proth witness: 5 is a quadratic non-residue, so p is prime.
    assert pow(5, (p - 1) // 2, p) == p - 1
    return p


def report_prime(n, p, label, t3_max=None, t4_cell=None):
    xs, counts_ceiling, counts_below = census(n, p)
    ceiling_stack = counts_ceiling[(3, 2)]
    t3_top, t3_winners = summarize(counts_ceiling)
    t4_top, t4_winners = summarize(counts_below)
    t4_sum, t4_weighted = checksum(counts_below, n)
    print(f"{label} p={p}: (3,2) t=3 {ceiling_stack}; t=3 max {t3_top} "
          f"({len(t3_winners)} pencils)")
    print(f"  t=4 below max {t4_top} at {t4_winners}")
    print(f"  t=4 census checksum: sum {t4_sum}, weighted {t4_weighted}")
    if t3_max is not None:
        assert t3_top == t3_max, (p, t3_top, t3_max)
    if t4_cell is not None:
        expected_max, expected_winners = t4_cell
        assert t4_top == expected_max, (p, t4_top, expected_max)
        if not isinstance(expected_winners, int):
            assert t4_winners == expected_winners, (p, t4_winners)
    # KKH26DimGeneralPin: the all-stack good-side bound #bad * 2 <= C(n,3).
    assert 2 * t4_top <= n * (n - 1) * (n - 2) // 6, (p, t4_top)
    return t3_top, t3_winners, t4_top, t4_winners, (t4_sum, t4_weighted)


def main():
    print("n=64 dimension-two below-ceiling monomial-pencil census (KKH26 rung)")
    print(f"t={T_CEIL} ceiling census and t={T_BELOW} below-ceiling census")

    # 1. Published order-eight integers of G310/G328.
    for p in (17, 41, 257):
        _, counts_ceiling, counts_below = census(8, p)
        expected = 16 if p == 17 else 40
        assert counts_ceiling[(3, 2)] == expected, (p, counts_ceiling[(3, 2)])
        maximum, winners = summarize(counts_below)
        assert maximum == 9 and winners == G328_WINNERS, (p, maximum, winners)
    print("n=8 reproduction: (3,2) t=3 count 40 (p=41,257) and 16 (p=17); "
          f"below-ceiling max 9 at {G328_WINNERS}")

    # 2. Published order-sixteen integers of PR #267.
    for p, (expected_ceiling, expected_max, expected_winners) in N16_SPOT.items():
        _, counts_ceiling, counts_below = census(16, p)
        assert counts_ceiling[(3, 2)] == expected_ceiling, (p, counts_ceiling[(3, 2)])
        maximum, winners = summarize(counts_below)
        assert maximum == expected_max, (p, maximum, expected_max)
        if expected_winners is not None:
            assert winners == expected_winners, (p, winners)
    print(f"n=16 reproduction: {len(N16_SPOT)} published spot primes, including "
          "the 353 exception (81) and the two-element-tie primes")

    prize = prize_prime()
    _, counts_ceiling, counts_below = census(16, prize)
    assert counts_ceiling[(3, 2)] == 464
    assert summarize(counts_below) == (97, N16_FOUR)
    print(f"n=16 prize-scale p = 21*2^128+1: (3,2) count 464, below max 97 at "
          f"{N16_FOUR}")

    # 3. Published order-thirtytwo integers of PR #272.
    for p, expected_stack, t3_winners_expected, t4_winners_expected in (
        (65537, 3264, N32_T3_WINNERS_65537, N32_T4_WINNERS_65537),
        (prize, 4512, None, char_pencils(32)),
    ):
        _, counts_ceiling, counts_below = census(32, p)
        assert counts_ceiling[(3, 2)] == expected_stack, (p,)
        t3_top, t3_winners = summarize(counts_ceiling)
        assert t3_top == N32_T3_MAX, (p, t3_top)
        if t3_winners_expected is not None:
            assert t3_winners == t3_winners_expected, (p, t3_winners)
        assert summarize(counts_below) == (N32_T4_MAX, t4_winners_expected), (p,)
    print("n=32 reproduction: (3,2) 3264 at p=65537 / 4512 at prize scale; "
          f"t=3 max {N32_T3_MAX}; t=4 below max {N32_T4_MAX} "
          f"(alongside ((16,31),(17,2)) at p=65537, the four character pencils "
          "at prize scale)")

    # 4. Held n=64 t=3 lane, reproduced through this code path.
    for p, expected_stack, expected_max in (
        (12289, 12160, N64_T3_MAX_12289),
        (65537, 13761, N64_T3_MAX_65537),
        (prize, 39744, N64_T3_MAX_PRIZE),
    ):
        _, counts_ceiling, _ = census(64, p)
        assert counts_ceiling[(3, 2)] == expected_stack, (p, counts_ceiling[(3, 2)])
        t3_top, t3_winners = summarize(counts_ceiling)
        assert t3_top == expected_max, (p, t3_top, expected_max)
        print(f"n=64 t=3 p={p}: (3,2) {expected_stack}; max {t3_top} at "
              f"{len(t3_winners)} pencils")
    _, counts_ceiling, _ = census(64, 65537)
    assert summarize(counts_ceiling)[1] == N64_T3_WINNERS_65537
    _, counts_ceiling, _ = census(64, prize)
    t3_winners = summarize(counts_ceiling)[1]
    assert len(t3_winners) == N64_T3_PRIZE_WINNER_COUNT
    assert all(pair in t3_winners for pair in N64_T3_PRIZE_SAMPLE)
    print("n=64 t=3 maximizer sets reproduced: ((11,18),(18,11),(47,54),(54,47)) "
          f"at p=65537, {N64_T3_PRIZE_WINNER_COUNT} pencils at prize scale")

    # 5. The new rung: full t=4 below-ceiling census at three primes.
    for p, t3_max, t4_cell, expected_checksum in (
        (12289, N64_T3_MAX_12289, N64_T4[12289], N64_T4_CHECKSUMS[12289]),
        (65537, N64_T3_MAX_65537, N64_T4[65537], N64_T4_CHECKSUMS[65537]),
        (prize, N64_T3_MAX_PRIZE, (7681, char_pencils(64)),
         N64_T4_PRIZE_CHECKSUM),
    ):
        result = report_prime(64, p, "n=64", t3_max=t3_max, t4_cell=t4_cell)
        assert result[4] == expected_checksum, (p, result[4])

    print("PASS: exact n=64 t=4 below-ceiling census on all 4096 monomial "
          "pencils at p = 12289, 65537 and the prize-scale prime; the published "
          "n=8/16/32 integers and the held n=64 t=3 maxima are reproduced by "
          "the same code path")
    print("prize-scale four-character-pencil cell: 7681")


if __name__ == "__main__":
    main()
