#!/usr/bin/env python3
"""Exact G104 primitive-concentration countercertificate at the first prize prime.

G104's (2,s-2)-split at s=13 requires the maximum primitive 11-tuple
sum-fiber to be at most

  floor(219!! / (C(110,13)^2 * 97! * (2^30)^2)).

The first eleven powers g^0,...,g^10 of the certified order-2^30 element
are subset-sum distinct. Hence they are zero-sum-free, and all 11!
permutations are primitive ordered tuples with one common sum. This gives
an exact lower bound on one primitive sum-fiber that exceeds both G104's
actual s=13 threshold and its proposed uniform 4*n^(2/3) majorant.
"""

from math import comb, factorial

P = 365375409332725729550921208179070755120141565953
N = 2**30
G = 303645430271030343624574566109998498685964493478
R = 110
S = 13
K = S - 2


def odd_double_factorial(m: int) -> int:
    out = 1
    for x in range(1, m + 1, 2):
        out *= x
    return out


xs = [pow(G, e, P) for e in range(K)]
assert len(set(xs)) == K
assert all(pow(x, N, P) == 1 for x in xs)

subset_sums: dict[int, int] = {}
for mask in range(1 << K):
    total = sum(xs[i] for i in range(K) if mask >> i & 1) % P
    if total in subset_sums:
        raise AssertionError(
            f"subset-sum collision: masks {subset_sums[total]} and {mask}"
        )
    subset_sums[total] = mask
assert subset_sums[0] == 0

common_sum = sum(xs) % P
permutation_fiber_floor = factorial(K)
wick = odd_double_factorial(2 * R - 1)
actual_threshold = wick // (comb(R, S) ** 2 * factorial(R - S) * N**2)
uniform_threshold = 4 * 2**20  # 4*n^(2/3), since n=2^30.

assert permutation_fiber_floor > actual_threshold
assert permutation_fiber_floor > uniform_threshold

print("G104 primitive-concentration factorial no-go: PASS")
print(f"P={P}")
print(f"n={N}, g={G}, order check g^n mod P={pow(G, N, P)}")
print(f"powers used=0..{K - 1}")
print(f"distinct subset sums={len(subset_sums)}=2^{K}; zero occurs only for empty subset")
print(f"common tuple sum={common_sum}")
print(f"primitive ordered-fiber lower bound={K}!={permutation_fiber_floor}")
print(f"G104 actual s={S} threshold={actual_threshold}")
print(f"factorial/actual={permutation_fiber_floor / actual_threshold:.12f}")
print(f"G104 uniform 4*n^(2/3) threshold={uniform_threshold}")
print(f"factorial/uniform={permutation_fiber_floor / uniform_threshold:.12f}")
print("witness powers:")
for e, x in enumerate(xs):
    print(f"  g^{e} = {x}")
