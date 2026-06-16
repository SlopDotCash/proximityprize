"""
Probe for the E3-closed-form rung (#444).

Target claim: zeroSumCount(mu_n, 6) = 15 n^3 - 45 n^2 + 40 n  EXACTLY for 2-power n.
zeroSumCount(mu_n, 6) = #{6-tuples (x1..x6) of n-th roots of unity with x1+..+x6 = 0}.

Confirm for n = 8, 16, 32 (2-power).
Confirm it FAILS for 3|n (n = 12, 24).

Also report zeroSumCount(mu_n, 4) = 9 n^2 - ? and zeroSumCount(mu_n,2) for sanity.
Uses an EXACT proper subgroup mu_n of F_p* (never the full group), per honesty contract.
"""
import sympy
from collections import Counter
from itertools import product


def subgroup(n):
    # need p with n | p-1, p prime, p large enough that mu_n is "generic"
    # (no spurious low-degree relations from the field). Take p large.
    m = (n ** 7 - 1) // n + 1
    while True:
        p = m * n + 1
        if sympy.isprime(p):
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            H = [pow(z, j, p) for j in range(n)]
            assert len(set(H)) == n
            assert len(H) < p - 1, "must be PROPER subgroup"
            return H, p
        m += 1


def zerosumcount(H, p, k):
    # exact count of k-tuples summing to 0 mod p, via convolution of the
    # "sum distribution". O(k * p) memory but p can be huge -> use dict convolution
    # Instead: build distribution of partial sums as Counter over residues.
    dist = Counter({0: 1})
    for _ in range(k):
        nd = Counter()
        for s, c in dist.items():
            for h in H:
                nd[(s + h) % p] += c
        dist = nd
    return dist[0]


def f3(n):
    return 15 * n ** 3 - 45 * n ** 2 + 40 * n


def f2_pred(n):
    # zeroSumCount(mu_n,4) char-0 closed form for 2-power n: 3n^2 - 3n + ... let's just measure
    return None


print("zeroSumCount(mu_n, 6) vs 15n^3 - 45n^2 + 40n")
print(f"{'n':>4} {'factor':>10} {'p':>12} {'Z6':>14} {'15n^3-45n^2+40n':>16} {'match':>6}")
for n in [8, 16, 32, 12, 24]:
    # p grows huge; cap the work. For n=32, p~n^7 ~ 3.4e10, 32^6=1e9 tuples but
    # convolution dict over residues is the bottleneck. Use moderate p but still
    # large enough to avoid spurious relations: p > (max partial sum) is automatic mod p,
    # we just need p with NO low-order relations among n-th roots beyond antipodal.
    H, p = subgroup(n)
    z6 = zerosumcount(H, p, 6)
    pred = f3(n)
    match = (z6 == pred)
    print(f"{n:>4} {str(sympy.factorint(n)):>10} {p:>12} {z6:>14} {pred:>16} {str(match):>6}")

print()
print("Sanity: zeroSumCount(mu_n, 2) (= n for even n) and zeroSumCount(mu_n,4):")
print(f"{'n':>4} {'Z2':>6} {'Z4':>10}")
for n in [8, 16, 32]:
    H, p = subgroup(n)
    z2 = zerosumcount(H, p, 2)
    z4 = zerosumcount(H, p, 4)
    print(f"{n:>4} {z2:>6} {z4:>10}")
