#!/usr/bin/env python3
"""Exact support-size decomposition of G133's signed puncture correction.

For ordered r-words a,b in an order-n multiplicative subgroup G of F_p^*, let

  E_s = #{(a,b): sum a=sum b, |supp(a)|=s},
  D_s = #{(a,b): sum a=sum b, supp(a) disjoint supp(b), |supp(a)|=s}.

Additive-character orthogonality gives the exact integer decomposition

  B_s = p E_s - A_s n^r,
  T_s = p D_s - A_s (n-s)^r,
  C_s = T_s-B_s,

where A_s is the number of left words having support size s.  Thus sum B_s is
the ordinary nonprincipal 2r-th moment, sum T_s is the centered fully-disjoint
census, and sum C_s is precisely G133's signed puncture correction.  No FFT or
floating point enters the certificate.

The falsifier is simple: if all C_s have one sign, or |sum C_s| is comparable
to sum |C_s|, then "cross-support signed cancellation" is not a new lever.  A
small cancellation ratio |sum C_s|/sum|C_s|, stable in proper p~n^4 cells,
keeps the lane alive and identifies which support sizes must be coupled.
"""

from collections import defaultdict
from itertools import product


def factor_distinct(x: int):
    out = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out


def primitive_root(p: int) -> int:
    factors = factor_distinct(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def subgroup(p: int, n: int):
    assert (p - 1) % n == 0 and n < p - 1
    z = pow(primitive_root(p), (p - 1) // n, p)
    G, x = [], 1
    for _ in range(n):
        G.append(x)
        x = x * z % p
    assert x == 1 and len(set(G)) == n
    return G


def analyze(p: int, n: int, r: int):
    G = subgroup(p, n)
    buckets = defaultdict(list)
    count = [0] * (r + 1)
    principal_disjoint = [0] * (r + 1)

    for idx in product(range(n), repeat=r):
        mask = 0
        total = 0
        for i in idx:
            mask |= 1 << i
            total += G[i]
        total %= p
        s = mask.bit_count()
        buckets[total].append(mask)
        count[s] += 1
        principal_disjoint[s] += (n - s) ** r

    equal = [0] * (r + 1)
    disjoint = [0] * (r + 1)
    for masks in buckets.values():
        k = len(masks)
        for left in masks:
            s = left.bit_count()
            equal[s] += k
            disjoint[s] += sum((left & right) == 0 for right in masks)

    nr = n**r
    base, total, corr = [0] * (r + 1), [0] * (r + 1), [0] * (r + 1)
    for s in range(1, r + 1):
        base[s] = p * equal[s] - count[s] * nr
        total[s] = p * disjoint[s] - principal_disjoint[s]
        corr[s] = total[s] - base[s]

    B, T, C = sum(base), sum(total), sum(corr)
    l1 = sum(abs(x) for x in corr)
    cancellation = abs(C) / l1 if l1 else 0.0
    print(f"CELL n={n} p={p} r={r} index={(p-1)//n} buckets={len(buckets)}")
    for s in range(1, r + 1):
        print(
            f"  s={s}: A={count[s]} E={equal[s]} D={disjoint[s]} "
            f"B={base[s]} T={total[s]} C={corr[s]}"
        )
    print(
        f"  SUM B={B} T={T} C={C} check={T == B + C} "
        f"cancel=|sum C_s|/sum|C_s|={cancellation:.8f} "
        f"relative=|C|/B={(abs(C)/B if B else 0.0):.8f}"
    )


if __name__ == "__main__":
    for cell in (
        (89, 8, 3),
        (233, 8, 3),
        (89, 8, 4),
        (233, 8, 4),
        (257, 16, 3),
        (65537, 16, 3),
        (65537, 16, 4),
        (1048609, 32, 3),
        (16777601, 64, 3),
    ):
        analyze(*cell)
