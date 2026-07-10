#!/usr/bin/env python3
"""#466 OC-TAIL probe: the cross-prime stacking-census tail ceiling.

Verifies, exactly, at n=16 (full pool) the three interface facts consumed by
`Frontier/_OCStackingTailCensusCeiling.lean` and the resulting ceiling:

  (a) certificate: for a support-6 height-1 negacyclic relation v, and prime
      p ≡ 1 mod 2m, p | N(v) := |Res(v, X^m+1)|  ⟺  v vanishes at some embedding mod p;
  (b) height ceiling: 0 < N(v) ≤ 6^m for every pool candidate (nonzero because the
      pool below is filtered to char-p-only candidates, i.e. N(v) ≠ 0);
  (c) cross-prime multiplicity: #{distinct primes p ≥ P dividing N(v)} ≤ log_P(6^m);

and then enumerates ALL violator primes in a long tail window and checks

  (#violators) * K ≤ (#candidates with N ≠ 0) * max-multiplicity   (K = n/16 orbits ~ here 1).

This is the double-count ceiling: it certifies FINITENESS of the depth-3 stacked
violator set in the tail, with an explicit poly(n)/log P cardinality bound.
"""

import itertools
import math
import sys

from sympy import Poly, resultant, symbols, isprime

X = symbols("x")


def norm_certificate(coeffs, m):
    """|Res(r, X^m + 1)| as an exact integer; coeffs indexed by exponent 0..m-1."""
    r = Poly(list(reversed(coeffs)), X)
    f = Poly([1] + [0] * (m - 1) + [1], X)  # X^m + 1
    return abs(int(resultant(r, f)))


def main():
    n, support = 16, 6
    m = n // 2
    M = 2 * m
    H_pow = 6 ** m
    P = 2 * n * n  # tail start P = 512 (β = 2.25); every prime ≥ P counted
    WINDOW_END = 120000

    # full pool
    pool = []
    for supp in itertools.combinations(range(m), support):
        for signs in itertools.product((1, -1), repeat=support):
            v = [0] * m
            for j, sg in zip(supp, signs):
                v[j] = sg
            pool.append(v)

    norms = [norm_certificate(v, m) for v in pool]
    nonzero = [(v, N) for v, N in zip(pool, norms) if N != 0]
    print(f"n={n} m={m} pool={len(pool)} char-p-only (N≠0): {len(nonzero)}")

    # (b) height ceiling
    okb = all(N <= H_pow for _, N in nonzero)
    print(f"(b) height ceiling N ≤ 6^m = {H_pow}: {okb}  (max N = {max(N for _, N in nonzero)})")

    # (c) cross-prime multiplicity vs log_P(6^m)
    D_bound = math.floor(math.log(H_pow) / math.log(P))
    worst = 0
    for _, N in nonzero:
        t = 0
        x = N
        d = 2
        primes = set()
        while d * d <= x:
            while x % d == 0:
                primes.add(d)
                x //= d
            d += 1
        if x > 1:
            primes.add(x)
        t = sum(1 for q in primes if q >= P)
        worst = max(worst, t)
    print(f"(c) max #distinct primes ≥ P={P} per candidate: {worst} ≤ floor(log_P 6^m) = {D_bound}: "
          f"{worst <= D_bound}")

    # (a)+(d): enumerate violator primes in the tail window; verify certificate at each
    K = max(1, n // 16)
    violators = []
    cert_ok = True
    p = P + (M - (P - 1) % M) % M + 1  # first p ≡ 1 mod M above P (approx; scan below)
    for p in range(P, WINDOW_END):
        if p % M != 1 or not isprime(p):
            continue
        # find embedding root
        w = None
        for g in range(2, p):
            cand = pow(g, (p - 1) // M, p)
            if pow(cand, M // 2, p) == p - 1:  # order exactly M
                w = cand
                break
        stacked = 0
        for v, N in nonzero:
            vanish = any(
                sum(cv * pow(w, (a * j) % M, p) for j, cv in enumerate(v)) % p == 0
                for a in range(1, M, 2) if math.gcd(a, M) == 1
            )
            if vanish != (N % p == 0):
                cert_ok = False
            if vanish:
                stacked += 1
        if stacked >= K:
            violators.append((p, stacked))

    ceiling = len(nonzero) * worst
    print(f"(a) certificate p|N ⟺ embedding-vanishing, all cells: {cert_ok}")
    print(f"(d) violator primes (≥{K} stacked) in [{P},{WINDOW_END}): {len(violators)}")
    print(f"    sample: {violators[:8]}")
    print(f"    ceiling |Cand_nz|*maxmult = {ceiling}; #violators*K = {len(violators) * K} ≤ ceiling: "
          f"{len(violators) * K <= ceiling}")
    ok = okb and worst <= D_bound and cert_ok and len(violators) * K <= ceiling
    print(f"ALL CHECKS: {ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
