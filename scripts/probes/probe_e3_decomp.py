"""
Structural decomposition of zero-sum 6-tuples of 2^mu-th roots of unity (#444).

Lam-Leung: for n = 2^mu, every vanishing sum of n-th roots is a Z-combination of
antipodal pairs {zeta^a, -zeta^a = zeta^{a+n/2}}. So a zero-sum 6-tuple, as a MULTISET
of 6 roots summing to 0, must partition into antipodal pairs {x, -x}.

Question: is EVERY zero-sum 6-tuple a union of 3 antipodal pairs?  (i.e. can it be
matched up so the 6 elements split into 3 pairs each summing to 0?)
Probe checks: for each ordered zero-sum 6-tuple, does the multiset of 6 values admit
a perfect matching into antipodal pairs?  If YES for all, the count is purely the
"3 antipodal pairs" count and we can get the closed form by inclusion-exclusion over
ordered tuples whose 6 positions pair up antipodally.

Then COUNT directly:
  N = # ordered 6-tuples (x1..x6) in mu_n^6 that partition into 3 antipodal pairs.
This equals sum over perfect matchings (15 of them) of [#tuples consistent with that
matching] minus overcounting where a tuple is consistent with MORE than one matching.
We compute N exactly by brute force AND by the inclusion-exclusion to cross-check the
closed form 15 n^3 - 45 n^2 + 40 n.
"""
import sympy
from itertools import product, combinations


def roots(n):
    # represent n-th roots as exponents in Z/n; -zeta^a = zeta^{a + n/2}
    return list(range(n))


def is_antipodal_pair(a, b, n):
    return (a - b) % n == n // 2


def all_perfect_matchings(positions):
    # positions: tuple of indices; yield list of pairs
    positions = list(positions)
    if not positions:
        yield []
        return
    first = positions[0]
    rest = positions[1:]
    for i in range(len(rest)):
        pair = (first, rest[i])
        remaining = rest[:i] + rest[i + 1:]
        for sub in all_perfect_matchings(remaining):
            yield [pair] + sub


MATCHINGS6 = list(all_perfect_matchings((0, 1, 2, 3, 4, 5)))


def tuple_has_antipodal_matching(t, n):
    for m in MATCHINGS6:
        if all(is_antipodal_pair(t[i], t[j], n) for (i, j) in m):
            return True
    return False


def brute_zerosum_6(n, p, z):
    # exact: count ordered 6-tuples of exponents whose roots sum to 0 mod p
    # AND check each is antipodally matchable
    vals = [pow(z, a, p) for a in range(n)]
    cnt = 0
    cnt_matchable = 0
    for t in product(range(n), repeat=6):
        s = sum(vals[a] for a in t) % p
        if s == 0:
            cnt += 1
            if tuple_has_antipodal_matching(t, n):
                cnt_matchable += 1
    return cnt, cnt_matchable


def subgroup(n):
    m = (n ** 7 - 1) // n + 1
    while True:
        p = m * n + 1
        if sympy.isprime(p):
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            return p, z
        m += 1


print("Check: is every zero-sum 6-tuple a union of 3 antipodal pairs? (2-power n)")
for n in [8, 16]:
    p, z = subgroup(n)
    cnt, matchable = brute_zerosum_6(n, p, z)
    pred = 15 * n ** 3 - 45 * n ** 2 + 40 * n
    print(f" n={n}: Z6={cnt}, antipodally-matchable={matchable}, "
          f"all matchable? {cnt == matchable}, =15n^3-45n^2+40n? {cnt == pred}")

# Now the inclusion-exclusion count of ordered 6-tuples that partition into 3 antipodal
# pairs. For a FIXED matching of the 6 positions into 3 pairs, the # of consistent
# ordered tuples is: choose x for each pair's first element freely (n ways), second is
# forced to -x. So n^3 per matching. There are 15 matchings. Naive sum = 15 n^3.
# Overcount: tuples consistent with >= 2 matchings. By inclusion-exclusion the exact
# count is 15n^3 - (corrections). Let's compute the exact count via set-union directly
# (count distinct tuples in the union of the 15 matching-consistent sets) for small n
# and confirm it equals 15n^3-45n^2+40n.

def union_count(n):
    seen = set()
    for m in MATCHINGS6:
        # iterate over the 3 free choices
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    t = [0] * 6
                    free = [a, b, c]
                    for k, (i, j) in enumerate(m):
                        t[i] = free[k]
                        t[j] = (free[k] + n // 2) % n  # antipode
                    seen.add(tuple(t))
    return len(seen)


print("\nInclusion-exclusion: |union of 15 antipodal-matching-consistent sets|")
for n in [2, 4, 8, 16]:
    uc = union_count(n)
    pred = 15 * n ** 3 - 45 * n ** 2 + 40 * n
    print(f" n={n}: union={uc}, 15n^3-45n^2+40n={pred}, match={uc == pred}")


# ---------------------------------------------------------------------------
# CHARACTERIZATION CROSS-CHECK (used by Frontier/_E3ClosedForm2Power.lean):
#   matchable(t) := the 6 positions partition into 3 antipodal pairs
#               <=> the value-distribution is symmetric under x -> x + n/2
#                   (count(x) == count(x+n/2) for every value x).
# This distribution form is what makes `matchable` cheaply decidable in Lean.
# Verify the two definitions coincide for all even n in a range (exhaustive).
# ---------------------------------------------------------------------------
def _matchable_by_matching(t, n):
    half = n // 2
    for m in MATCHINGS6:
        if all((t[i] - t[j]) % n == half for (i, j) in m):
            return True
    return False


def _matchable_by_distribution(t, n):
    half = n // 2
    from collections import Counter
    c = Counter(t)
    return all(c[x] == c[(x + half) % n] for x in set(t))


def _check_characterization():
    print("\nCharacterization cross-check (matching-partition <=> distribution-symmetry):")
    for n in [2, 4, 6, 8]:
        mism = 0
        for t in product(range(n), repeat=6):
            if _matchable_by_matching(t, n) != _matchable_by_distribution(t, n):
                mism += 1
        print(f"  n={n}: mismatches = {mism}/{n**6} (0 => characterizations agree)")


if __name__ == "__main__":
    _check_characterization()
