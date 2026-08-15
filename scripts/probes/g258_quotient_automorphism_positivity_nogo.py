#!/usr/bin/env python3
"""G258: exact positivity/support-preserving quotient-automorphism reversal.

G257 permuted conjugate Fourier pairs and found negative covariance, but most
unconstrained optima inverted to signed physical profiles. Fable G258 therefore
proposed positivity plus sparse support as the first surviving invariant.

A cyclic quotient automorphism is an exact admissible move that this local
search missed. For every unit a mod m, set w_a(x)=w(a^{-1}x). Then:
  * w_a is an integer nonnegative relabeling of w, with identical support size;
  * DFT(w_a)(k)=DFT(w)(a*k), so the complete Fourier-value multiset and
    conjugation pairing are preserved exactly;
  * the covariance against the fixed rank profile can nevertheless change sign.

All reported covariance values are Python integers computed in physical space:
  m*sum_x w_a(x)r(x) - (sum w_a)(sum r).
No floating point or FFT enters the certificate.
"""
from __future__ import annotations
import math
import numpy as np


def prime_factors(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int, root: int) -> list[int]:
    z = pow(root, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def subset_hists(G: list[int], p: int, max_rank: int) -> np.ndarray:
    dp = np.zeros((max_rank + 1, p), dtype=np.int64)
    dp[0, 0] = 1
    for used, x in enumerate(G, start=1):
        for rank in range(min(max_rank, used), 0, -1):
            dp[rank] += np.roll(dp[rank - 1], x)
    for rank in range(max_rank + 1):
        assert int(dp[rank].sum()) == math.comb(len(G), rank)
    return dp


def circ_corr_exact(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Exact integer c[t]=sum_s a[s]b[s-t], with no FFT or rounding."""
    p = len(a)
    b_neg = b[(-np.arange(p)) % p]
    out = np.zeros(p, dtype=np.int64)
    for s, value in enumerate(a):
        if value:
            out += value * np.roll(b_neg, s)
    assert int(out.sum()) == int(a.sum()) * int(b.sum())
    return out


def profiles(n: int, p: int, r: int):
    root = primitive_root(p)
    m = (p - 1) // n
    G = subgroup(p, n, root)
    reps = [pow(root, j, p) for j in range(m)]
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    dp = subset_hists(G, p, r)
    R = circ_corr_exact(dp[r], dp[r - 1])
    return m, [int(W[x]) for x in reps], [int(R[x]) for x in reps]


def relabel(w: list[int], a: int) -> list[int]:
    m = len(w)
    ai = pow(a, -1, m)
    return [w[(ai * x) % m] for x in range(m)]


def centered_cov(w: list[int], r: list[int]) -> int:
    m = len(w)
    return m * sum(x * y for x, y in zip(w, r)) - sum(w) * sum(r)


def scan_cell(n: int, p: int, ranks=(5, 6)):
    rows = {}
    base_w = None
    m = None
    for rank in ranks:
        m0, w, rr = profiles(n, p, rank)
        assert m is None or m == m0
        assert base_w is None or w == base_w
        m, base_w = m0, w
        units = [a for a in range(1, m) if math.gcd(a, m) == 1]
        vals = [(centered_cov(relabel(w, a), rr), a) for a in units]
        vals.sort()
        rows[rank] = (centered_cov(w, rr), vals[0], sum(c < 0 for c, _ in vals), rr)
    common = []
    for a in range(1, m):
        if math.gcd(a, m) != 1:
            continue
        cs = tuple(centered_cov(relabel(base_w, a), rows[r][3]) for r in ranks)
        if all(c < 0 for c in cs):
            common.append((a, cs))
    print(f"n={n} p={p} m={m} support={sum(x != 0 for x in base_w)} "
          f"nonneg={min(base_w) >= 0} integral={all(isinstance(x,int) for x in base_w)}")
    for rank in ranks:
        base, best, neg, _ = rows[rank]
        print(f"  r={rank}: base={base:+d} best={best[0]:+d}@a={best[1]} "
              f"negative_units={neg}/{sum(math.gcd(a,m)==1 for a in range(1,m))}")
    print(f"  simultaneous_negative={common[:12]} total={len(common)}")
    return m, base_w, rows, common


def euler_phi_from_factorization(factors: dict[int, int]) -> tuple[int, int]:
    value = 1
    phi = 1
    for prime, exponent in factors.items():
        value *= prime ** exponent
        phi *= (prime - 1) * prime ** (exponent - 1)
    return value, phi


def main():
    print("# G258 exact quotient-automorphism positivity/support no-go")
    m, w, rows, common = scan_cell(16, 1297)
    assert m == 81
    assert set(x for x in w) <= {0, 1} and sum(w) == 16 and sum(x != 0 for x in w) == 16
    moved = relabel(w, 26)
    assert set(moved) <= {0, 1} and sum(moved) == 16 and sum(x != 0 for x in moved) == 16
    exact = {5: (496733, 113689, 93845, 1261081, -346283),
             6: (2185369, 477249, 417335, 3691265, -1161769)}
    for rank, (sum_r, sum_wr, sum_moved_r, base_cov, moved_cov) in exact.items():
        rr = rows[rank][3]
        assert sum(rr) == sum_r
        assert sum(x*y for x, y in zip(w, rr)) == sum_wr
        assert sum(x*y for x, y in zip(moved, rr)) == sum_moved_r
        assert centered_cov(w, rr) == base_cov > 0
        assert centered_cov(moved, rr) == moved_cov < 0
    assert any(a == 26 and cs == (-346283, -1161769) for a, cs in common)
    print("  a=26 exact: inverse=53, base support=", [i for i,x in enumerate(w) if x])
    print("              moved support=", [i for i,x in enumerate(moved) if x])
    print("  exact physical certificate PASS: same unit reverses r=5 and r=6")
    print("# controls")
    for cell in [(8, 1801), (32, 641), (64, 3329), (32, 3617)]:
        scan_cell(*cell)
    print("# sponsor automorphism-family sizes")
    sponsor_factors = {
        "P1": {2: 6, 7: 3, 26407: 1, 279991: 1, 4533259: 1,
               462478642316479903: 1},
        "P2": {3: 1, 5: 2, 7: 1, 71: 1, 202172094073993: 1,
               90308905535905320959: 1},
    }
    expected = {"P1": 2**128 + 192, "P2": 2**129 + 13}
    for name, factors in sponsor_factors.items():
        value, phi = euler_phi_from_factorization(factors)
        assert value == expected[name]
        floor_log2 = phi.bit_length() - 1
        print(f"  {name}: m={value} phi(m)={phi} > 2^{floor_log2}")

if __name__ == "__main__":
    main()
