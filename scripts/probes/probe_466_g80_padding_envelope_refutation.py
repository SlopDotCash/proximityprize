#!/usr/bin/env python3
"""Exact refutation of R369/G80's ordered-tuple padding envelope.

At H=mu_4 in F_3001 and the exact saddle r=ceil(log 3001)=9, enumerate multiplicity
vectors.  Maximal common-multiset cancellation leaves primitive depth s=2.  The proposed
envelope omits the independent ordering of the common padding on the second endpoint.

All arithmetic below is exact Python integer arithmetic; no FFT or floating count is used.
"""

import itertools
import math


P = 3001
Z = 1353
N = 4
R = 9
S = 2


def weak_compositions(total: int, parts: int):
    """Yield every length-parts nonnegative vector summing to total."""
    for bars in itertools.combinations(range(total + parts - 1), parts - 1):
        points = (-1,) + bars + (total + parts - 1,)
        yield tuple(points[i + 1] - points[i] - 1 for i in range(parts))


def multinomial(counts):
    answer = math.factorial(sum(counts))
    for count in counts:
        answer //= math.factorial(count)
    return answer


def add_vectors(left, right):
    return tuple(a + b for a, b in zip(left, right))


def main():
    subgroup = tuple(pow(Z, j, P) for j in range(N))
    assert subgroup == (1, 1353, 3000, 1648)
    assert pow(Z, 2, P) == P - 1 and pow(Z, 4, P) == 1
    assert P >= N**4
    assert math.ceil(math.log(P)) == R

    # The only disjoint depth-two zero-sum histogram pair is the antipodal partition,
    # in either orientation.  Each side has two orders: J_2 = 2*2*2 = 8 ordered cores.
    a = (1, 0, 1, 0)  # {1,-1}
    b = (0, 1, 0, 1)  # {i,-i}
    assert sum(c * x for c, x in zip(a, subgroup)) % P == 0
    assert sum(c * x for c, x in zip(b, subgroup)) % P == 0
    core_hist_pairs = ((a, b), (b, a))
    ordered_core_count = sum(multinomial(x) * multinomial(y) for x, y in core_hist_pairs)
    assert ordered_core_count == 8

    padding_depth = R - S
    sector_mass = 0
    for core_left, core_right in core_hist_pairs:
        for padding in weak_compositions(padding_depth, N):
            full_left = add_vectors(core_left, padding)
            full_right = add_vectors(core_right, padding)
            # Since the cores are disjoint, componentwise min(full_left,full_right)=padding:
            # maximal common cancellation has depth exactly S.
            assert tuple(min(x, y) for x, y in zip(full_left, full_right)) == padding
            sector_mass += multinomial(full_left) * multinomial(full_right)

    desc = math.prod(range(R - S + 1, R + 1))
    claimed = ordered_core_count * desc**2 * N**padding_depth
    corrected_safe = claimed * math.factorial(padding_depth)

    print(f"p={P} H={subgroup} p>=n^4={P >= N**4} saddle={math.ceil(math.log(P))}")
    print(f"r={R} s={S} J_s={ordered_core_count}")
    print(f"exact W_r^(s)={sector_mass}")
    print(f"claimed envelope={claimed}")
    print(f"excess={sector_mass - claimed} ratio={sector_mass / claimed:.12f}")
    print(f"safe factorial-corrected envelope={corrected_safe}")

    assert sector_mass == 1_148_084_928
    assert claimed == 679_477_248
    assert sector_mass > claimed
    assert sector_mass <= corrected_safe
    print("VERDICT: CLAIMED PADDING ENVELOPE REFUTED; FACTORIAL-CORRECTED ENVELOPE SURVIVES")


if __name__ == "__main__":
    main()
