#!/usr/bin/env python3
"""Check a counterexample to two sharp estimates on a thin dyadic subgroup.

For each specified prime, one frequency coset refutes the sharp square-root
constant and the unit DC-subtracted Wick bound at a range of depths. The
second range includes ceil(log(p)). All checks use integers or fractions.
Three further primes around the production density exponent give depth-two
counterexamples by short three-term relations. None of the finite checks
addresses an unspecified absolute constant.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from math import factorial, isqrt, prod


N = 64
# Each row contains p, a subgroup generator, a frequency, a strict lower
# bound on the absolute period, and the depths tested for a Wick violation.
WITNESSES = (
    (16_802_369, 10_536_220, 8_954_665, Fraction(4089, 100), range(11, 16)),
    (16_890_817, 13_992_976, 4_780_558, Fraction(4231, 100), range(9, 21)),
)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def cosine_upper(residue, p):
    """Bound cos(2*pi*residue/P) above by a rational number."""
    # Reduce the true angle to [0, pi], then round it down using 3.14 < pi.
    # Cosine decreases on this interval. Its degree-12 Taylor polynomial
    # is an upper bound: the remaining alternating terms decrease in size.
    t = Fraction(628 * min(residue, p - residue), 100 * p)
    return sum((-1) ** i * t ** (2 * i) / factorial(2 * i) for i in range(7))


def additive_energy(subgroup, depth, p):
    """Count ordered pairs of depth-tuples with matching sums in F_P."""
    # Normalize the first summand to 1. Multiplicative cosets of H have
    # identifiers x**N because the kernel of this power map is H.
    order = len(subgroup)
    normalized = Counter()
    for tail in combinations_with_replacement(subgroup, depth - 1):
        residue = (1 + sum(tail)) % p
        permutations = factorial(depth - 1) // prod(
            factorial(count) for count in Counter(tail).values()
        )
        normalized[pow(residue, order, p)] += permutations
    check(sum(normalized.values()) == order ** (depth - 1), "incorrect normalized count")
    # For a nonzero coset, each field element in it has normalized[coset]
    # unrestricted representations. Every normalized zero sum yields N
    # unrestricted zero sums, all at the single field element 0.
    zero_count = order * normalized.pop(0, 0)
    return zero_count ** 2 + order * sum(count ** 2 for count in normalized.values())


def verify(prime, generator, frequency, period_lower, depths):
    check(all(prime % d for d in range(2, isqrt(prime) + 1)), "composite modulus")
    index, remainder = divmod(prime - 1, N)
    check(remainder == 0 and index % 2 == 1, "incorrect 2-adic valuation")
    check(N ** 4 < prime < 2 * N ** 4, "outside the thin prime band")
    check(pow(generator, N // 2, prime) == prime - 1, "incorrect half power")
    subgroup = [pow(generator, k, prime) for k in range(N)]
    check(len(set(subgroup)) == N and pow(generator, N, prime) == 1, "incorrect order")
    check(0 < frequency < prime, "principal or unreduced frequency")
    # The period is real because H = -H.
    upper = sum(cosine_upper(frequency * x % prime, prime) for x in subgroup)
    check(upper < -period_lower, "period certificate failed")
    print(f'p={prime}, n={N}, m={index}, eta_b < -{period_lower}')

    # log(m) < 25/2 by the positive series for exp(25/2).
    exp_partial = sum(Fraction(25, 2) ** i / factorial(i) for i in range(26))
    check(index < exp_partial, "log(index) upper bound failed")
    check(2 * N * Fraction(25, 2) < period_lower ** 2, "sharp bound did not fail")
    print('Certified |eta_b| > sqrt(2*n*log(m)).')

    for depth in range(2, 6):
        energy = additive_energy(subgroup, depth, prime)
        wick = prod(range(1, 2 * depth, 2)) * N ** depth
        excess = prime * energy - N ** (2 * depth) - prime * wick
        check(excess < 0, f"shallow Wick bound failed at depth {depth}")
        print(f'r={depth}, E_r={energy}, p*E_r-n^(2r)-p*Wick={excess}')

    for depth in depths:
        wick = prod(range(1, 2 * depth, 2)) * N ** depth
        # Each nonzero frequency in bH gives the same period. Character
        # orthogonality identifies the full nonprincipal moment with
        # p*E_r-n^(2r), so this one coset already rules out the unit bound.
        check(N * period_lower ** (2 * depth) > prime * wick,
              f"single-coset Wick violation failed at depth {depth}")
    print(f'r={depths.start}..{depths.stop-1}, single coset bH exceeds p*Wick.')

    if 17 in depths:
        # 8/3 < e < 11/4 by its series: after 1/3! the tail lies strictly
        # between 0 and (1/4!) / (1-1/5). These rational comparisons locate
        # both endpoints of the optimized logarithmic moment tests.
        check(Fraction(11, 4) ** 16 < prime < Fraction(8, 3) ** 17,
              "ceil(log(p)) is not certified as 17")
        check(Fraction(11, 4) ** 12 < index < Fraction(8, 3) ** 13,
              "ceil(log(m)) is not certified as 13")
        print('Certified ceil(log(m))=13 and ceil(log(p))=17.')


def verify_three_term_witness(n, prime, h, exponent, expected_energy):
    check(all(prime % d for d in range(2, isqrt(prime) + 1)), "composite modulus")
    check(pow(h, n // 2, prime) == prime - 1, "incorrect half power")
    subgroup = [pow(h, k, prime) for k in range(n)]
    check(pow(h, n, prime) == 1 and len(set(subgroup)) == n, "incorrect order")
    check(len({1, h, subgroup[exponent]}) == 3, "trivial arithmetic progression")
    check((h + subgroup[exponent]) % prime == 2, "progression relation failed")
    # The actual exponent lies in (5.25, 5.3) for every row. The trial
    # divisions, subgroup powers and ordered-pair counts are all exact.
    check(n ** 21 < prime ** 4 and prime ** 10 < n ** 53, "outside density band")
    pair_sums = Counter((x + y) % prime for x in subgroup for y in subgroup)
    energy = sum(count ** 2 for count in pair_sums.values())
    check(energy == expected_energy == additive_energy(subgroup, 2, prime),
          "independent ordered-pair counts disagree")
    excess = prime * energy - n ** 4 - 3 * prime * n ** 2
    check(excess > 0, "depth-two unit Wick bound did not fail")
    print(f'n={n}, p={prime}, 2=h+h^{exponent}, E_2={energy}, excess={excess}')


if __name__ == '__main__':
    for witness in WITNESSES:
        verify(*witness)

    for progression in (
        (64, 3_183_784_129, 1_380_119_153, 24, 12_864),
        (64, 3_322_894_721, 3_120_650_132, 58, 12_864),
        (128, 133_759_945_217, 6_645_390_832, 98, 50_304),
    ):
        verify_three_term_witness(*progression)
