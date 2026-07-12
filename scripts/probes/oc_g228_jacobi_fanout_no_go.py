#!/usr/bin/env python3
"""G228 quotient-Jacobi fanout no-go.

This probe records the exact character identity behind the live analytic lane.
For G=mu_n <= F_p^*, m=(p-1)/n, and quotient characters chi_k trivial on G,

  S_k := sum_{u in G} conj(chi_k)(2-u)
       = (1/m) sum_{a=0}^{m-1} lambda_a(2) conj(chi_k)(2)
             J(lambda_a, conj(chi_k)),

where lambda_a ranges over the same quotient-character group and J is the
standard finite-field Jacobi sum with chars extended by 0 at zero.  The Mellin
weight used by the CORE covariance is What(k)=n*S_k.

Each non-exceptional Jacobi summand has magnitude sqrt(p).  Therefore any K
summands in this inner Jacobi expansion have pointwise size <= n*K*sqrt(p)/m.
Parseval over the quotient classes gives

  sum_{k=1}^{m-1} |S_k|^2 = m * sum_C c_C^2 - z^2,
  c_C = #{u in G : 2-u in C},    z = sum_C c_C = #{u in G : 2-u != 0}.

At the sponsor primes 2 is not in G, so z=n.  Since c_C are then nonnegative
integers summing to n and m >= n, sum_C c_C^2 >= n.  Thus the full What has
RMS at least n*sqrt(n*(m-n)/(m-1)), while K Jacobi summands have RMS at most
n*K*sqrt(p)/m.  At the sponsor primes this ratio is <= K/sqrt(m) up to
negligible factors, so any bounded Jacobi subfamily is RMS-negligible.  A
constant-fraction recovery needs K = Omega(sqrt(m)), not O(1).
"""
from __future__ import annotations

import cmath
import math
from collections import Counter


def factor(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise RuntimeError(f"no primitive root for {p}")


def subgroup(p: int, n: int, root: int) -> list[int]:
    z = pow(root, (p - 1) // n, p)
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x * z) % p
    assert x == 1 and len(set(G)) == n
    return G


def dlog_table(p: int, root: int) -> dict[int, int]:
    logs = {}
    x = 1
    for e in range(p - 1):
        logs[x] = e
        x = (x * root) % p
    assert x == 1 and len(logs) == p - 1
    return logs


def qchar_value(exp_mod_m: int, m: int, x: int, logs: dict[int, int]) -> complex:
    if x == 0:
        return 0j
    return cmath.exp(2j * math.pi * (exp_mod_m * (logs[x] % m)) / m)


def jacobi_sum(p: int, m: int, a: int, b: int, logs: dict[int, int]) -> complex:
    total = 0j
    for x in range(p):
        total += qchar_value(a, m, x, logs) * qchar_value(b, m, (1 - x) % p, logs)
    return total


def direct_S(p: int, m: int, k: int, G: list[int], logs: dict[int, int]) -> complex:
    total = 0j
    for u in G:
        v = (2 - u) % p
        # conjugate quotient character chi_k at v
        total += qchar_value((-k) % m, m, v, logs)
    return total


def jacobi_expansion_S(p: int, m: int, k: int, logs: dict[int, int]) -> complex:
    # S_k = 1/m sum_a lambda_a(2) conj(chi_k)(2) J(lambda_a, conj(chi_k)).
    chi2 = qchar_value((-k) % m, m, 2 % p, logs)
    total = 0j
    for a in range(m):
        total += qchar_value(a, m, 2 % p, logs) * chi2 * jacobi_sum(p, m, a, (-k) % m, logs)
    return total / m


def class_counts(p: int, n: int, m: int, G: list[int], logs: dict[int, int]) -> Counter[int]:
    counts: Counter[int] = Counter()
    for u in G:
        v = (2 - u) % p
        if v != 0:
            counts[logs[v] % m] += 1
    return counts


def row(p: int, n: int, check_jacobi: bool = False) -> None:
    assert (p - 1) % n == 0
    m = (p - 1) // n
    root = primitive_root(p)
    logs = dlog_table(p, root)
    G = subgroup(p, n, root)
    counts = class_counts(p, n, m, G, logs)
    z = sum(counts.values())
    sumsq = sum(c * c for c in counts.values())
    nonzero_energy = m * sumsq - z * z
    mean_s2 = nonzero_energy / (m - 1) if m > 1 else 0.0
    one_term_rms_ratio = math.sqrt(p) / (m * math.sqrt(mean_s2)) if mean_s2 else float("inf")
    needs = {theta: math.ceil(theta / one_term_rms_ratio) for theta in (0.1, 0.5, 0.9)}
    coll_hist = Counter(counts.values())
    print(
        f"n={n:<4} p={p:<7} m={m:<5} occupied={len(counts):<4} "
        f"class_hist={dict(sorted(coll_hist.items()))} mean|S|^2={mean_s2:.6g} "
        f"K_ratio={one_term_rms_ratio:.6g} K_for_10/50/90={needs[0.1]}/{needs[0.5]}/{needs[0.9]}"
    )
    if check_jacobi:
        errs = []
        for k in range(1, m):
            d = direct_S(p, m, k, G, logs)
            e = jacobi_expansion_S(p, m, k, logs)
            errs.append(abs(d - e))
        print(f"  jacobi_identity_max_err={max(errs):.3e} over {m-1} nontrivial modes")


def production_bound(label: str, n: int, m: int) -> None:
    p = n * m + 1
    # The sponsor primes satisfy 2 notin G, so z=n.  The lower bound uses
    # sum_C c_C^2 >= n, valid when m >= n and z=n.
    assert pow(2, n, p) != 1
    mean_s2_lb = n * (m - n) / (m - 1)
    one_term_ratio_ub = math.sqrt(p) / (m * math.sqrt(mean_s2_lb))
    needs = {theta: math.ceil(theta / one_term_ratio_ub) for theta in (0.1, 0.5, 0.9)}
    print(
        f"{label}: n=2^30 m={m} log2(m)={math.log2(m):.6f} "
        f"one_jacobi_RMS_ratio<=2^{math.log2(one_term_ratio_ub):.3f} "
        f"K_for_10/50/90>={needs[0.1]}/{needs[0.5]}/{needs[0.9]} "
        f"(~sqrt(m)=2^{0.5*math.log2(m):.3f})"
    )


def main() -> None:
    print("Exact finite cells; K_ratio is the RMS fraction contributed by one inner Jacobi summand.")
    for p, n, check in [
        (41, 8, True),
        (97, 16, True),
        (257, 16, True),
        (1009, 8, False),
        (1297, 16, False),
        (2593, 32, False),
        (4673, 64, False),
        (65537, 16, False),
        (65537, 32, False),
        (65537, 64, False),
    ]:
        if (p - 1) % n == 0:
            row(p, n, check)
    print("\nSponsor-prime lower bounds, no enumeration used.")
    n = 2**30
    production_bound("P1", n, 2**128 + 192)
    production_bound("P2", n, 2 * 2**128 + 13)


if __name__ == "__main__":
    main()
