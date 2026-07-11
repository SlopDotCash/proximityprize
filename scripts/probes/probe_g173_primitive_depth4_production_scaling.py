#!/usr/bin/env python3
"""Audit G105's primitive-relation suppression extrapolation.

For a multiplicative subgroup H=mu_n in F_p, enumerate unordered disjoint pairs of
4-subsets A,B with sum(A)=sum(B) mod p.  A pair is primitive iff it has no balanced
proper subcore.  For disjoint 4-subsets, depths 1 and 3 are impossible (the latter
would force equality of the complementary singleton), so primitivity is exactly the
absence of an equal-sum 2-subset across A and B.

The deployed shape has log_n p ~= 158/30 = 5.266....  Small n=16,32,64 cells do show
total suppression at depth 4, unlike random controls.  This is useful evidence but not
a field-size transfer theorem: the same script verifies the exact dyadic depth-2
accident at n=64, p=17318209>64^4, formalized in G173.  Therefore `p>n^4` is already
a false threshold, and zero depth-4 samples cannot be extrapolated to all primitive
lengths or to the certified production primes.
"""
from collections import defaultdict
from itertools import combinations
from math import comb, log
import random
import sympy as sp

BETA = 158 / 30


def v2(x):
    c = 0
    while x % 2 == 0:
        c += 1
        x //= 2
    return c


def production_like_prime(n):
    target = int(round(n ** BETA))
    k = max(1, target // n)
    if k % 2 == 0:
        k += 1
    while True:
        p = n * k + 1
        if sp.isprime(p):
            assert v2(p - 1) == n.bit_length() - 1
            return p
        k += 2


def subgroup(p, n):
    primitive = sp.primitive_root(p)
    z = pow(primitive, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x)
        x = x * z % p
    assert x == 1 and len(set(H)) == n
    return H


def primitive_collision_count(S, p):
    by_sum = defaultdict(list)
    for I in combinations(range(len(S)), 4):
        by_sum[sum(S[i] for i in I) % p].append(I)
    total = primitive = 0
    witnesses = []
    for bucket in by_sum.values():
        for j in range(len(bucket)):
            A = bucket[j]
            setA = set(A)
            pair_sums_A = { (S[A[u]] + S[A[v]]) % p
                            for u, v in combinations(range(4), 2) }
            for k in range(j):
                B = bucket[k]
                if setA.intersection(B):
                    continue
                total += 1
                reducible = any((S[B[u]] + S[B[v]]) % p in pair_sums_A
                                for u, v in combinations(range(4), 2))
                if not reducible:
                    primitive += 1
                    if len(witnesses) < 3:
                        witnesses.append(([S[i] for i in A], [S[i] for i in B]))
    return total, primitive, witnesses, len(by_sum)


def run_cell(n):
    p = production_like_prime(n)
    H = subgroup(p, n)
    total, primitive, witnesses, occupied = primitive_collision_count(H, p)
    N = comb(n, 4)
    expected = N * (N - 1) / (2 * p)
    print(f"n={n} p={p} beta={log(p,n):.6f} v2={v2(p-1)} C(n,4)={N}")
    print(f"  subgroup: all_disjoint={total} primitive={primitive} occupied_sums={occupied} birthday={expected:.3f}")
    for A, B in witnesses:
        print(f"  witness A={A} B={B} sum={sum(A)%p}")
    random.seed(1000 + n)
    R = random.sample(range(1, p), n)
    rt, rp, _, ro = primitive_collision_count(R, p)
    print(f"  random:   all_disjoint={rt} primitive={rp} occupied_sums={ro}")
    return primitive


def check_known_threshold_counterexample():
    p, n, omega = 17318209, 64, 7937154
    assert sp.isprime(p) and p > n ** 4 and v2(p - 1) == 6
    assert pow(omega, n, p) == 1 and pow(omega, n // 2, p) == p - 1
    a, b, c = pow(omega, 52, p), pow(omega, 57, p), pow(omega, 58, p)
    assert (a + b - c - 1) % p == 0
    assert a != 1 and b != 1 and not (c == p - 1 and b == (-a) % p)
    print(f"known dyadic p>n^4 counterexample: n={n} p={p} omega={omega}")
    print(f"  normalized accident a={a} b={b} c={c}: a+b=c+1, outside Mann families")


def main():
    vals = [run_cell(n) for n in (16, 32, 64)]
    assert vals == [0, 0, 0]
    check_known_threshold_counterexample()


if __name__ == "__main__":
    main()
