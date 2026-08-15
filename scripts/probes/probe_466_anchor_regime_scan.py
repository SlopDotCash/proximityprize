#!/usr/bin/env python3
"""Anchor-failure regime scan (#466, census-tower coordinates).

For multiplicative subgroups H of order n in ZMod p across regimes p ~ n^e
(e = 2..5), measures the exact rung-t anchor ratio

    rho(t) = q*E_t / (q*(2t-1)!!*n^t + n^(2t)),

where E_t is the t-fold additive energy (computed exactly by iterated sumset
convolution). Anchor PASSES iff rho <= 1.

Motivation: the (64, 16778497, 5) DCEnergy counterexample sits at n^4/q = 0.99997
(its crossover), fails at rung 5 with a healthy disjoint census. Production
(n = 2^30, q ~ 2^158) has its crossover between rungs 5 and 6. This scan tests the
"failures live at the crossover" hypothesis systematically.

Usage: python3 probe_466_anchor_regime_scan.py
"""

from collections import Counter
from math import log


def dfact(m: int) -> int:
    r = 1
    while m > 0:
        r *= m
        m -= 2
    return r


def is_prime(m: int) -> bool:
    if m < 2:
        return False
    d = 2
    while d * d <= m:
        if m % d == 0:
            return False
        d += 1
    return True


def find_gen(p: int) -> int:
    fact = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fact.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fact.append(m)
    for g in range(2, 1000):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fact):
            return g
    raise RuntimeError


def subgroup(p: int, n: int):
    g = find_gen(p)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x)
        x = x * h % p
    assert len(set(H)) == n
    return H


def energies(p: int, H, tmax: int):
    """E_t for t = 1..tmax via iterated convolution of the sum-representation dict."""
    out = {}
    S = Counter({0: 1})
    for t in range(1, tmax + 1):
        T = Counter()
        for v, c in S.items():
            for h in H:
                T[(v + h) % p] += c
        S = T
        out[t] = sum(c * c for c in S.values())
    return out


def main():
    n_list = [(16, [3, 4, 5]), (32, [3, 4]), (64, [2, 3])]
    print("regime scan: rho(t) = q*E_t / (q*(2t-1)!!*n^t + n^(2t));  FAIL iff rho > 1")
    for n, exps in n_list:
        for e in exps:
            # first prime p ≡ 1 (mod n) at or above n^e
            p = n ** e + 1
            while not (is_prime(p) and (p - 1) % n == 0):
                p += 1
            if n * p > 8 * 10 ** 7:
                continue
            H = subgroup(p, n)
            tmax = 6
            E = energies(p, H, tmax)
            # crossover rung: smallest t with n^t > p*(2t-1)!!
            cross = next((t for t in range(1, 12)
                          if n ** t > p * dfact(2 * t - 1)), None)
            row = []
            for t in range(2, tmax + 1):
                num = p * E[t]
                den = p * dfact(2 * t - 1) * n ** t + n ** (2 * t)
                row.append((t, num / den))
            marks = " ".join(f"t{t}:{r:7.4f}{'F' if r > 1 else ' '}" for t, r in row)
            print(f"n={n:3d} e={e} p={p:9d} n^e/p={n**e/p:6.4f} cross~t{cross}: {marks}")


if __name__ == "__main__":
    main()
