#!/usr/bin/env python3
"""#466 W12: dominant-relation repair census for the saturation route.

BinomialBadPrimeLaw is refuted (probe_w12_binomial_bad_prime_refutation.py): no realized
binomial with |Res| | 8p exists at any in-window prime for n>=32.  The r325 return bound
also covers the wider DOMINANT class (`dominant_max_bound`): any relation f with one
coefficient exceeding the l1-mass of the rest.  The repaired open input would be:

  DominantBadPrimeLaw: every in-window K-bad prime admits a realized dominant relation f
  (support >= 3, |f_top| > sum |f_rest|, height <= 8) with |Res(x^16+1, f)| | 2^t * p.

This probe enumerates ALL dominant trinomials with support containing 0 (wlog: x^u is a
unit with Res(x^u f) = +-Res(f)), height <= 8, over all 92 census K-bad primes:
  f = c0 + c1 x^i + c2 x^j,  1 <= c0 <= 8 (wlog global sign), c1,c2 in [-8..8]\\{0},
  max|coeff| > sum of the other two.
Realization is checked at the 16 roots of x^16 = -1 mod p; exact resultants (sympy) are
computed for realized candidates only.  Reports, per prime, realized dominant relations
with Res/p a power of two (t<=3 and any t).  Also runs the n=64 endpoint p=16778497.
"""

from __future__ import annotations

import re
import sys
from itertools import combinations
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent


def element_of_order(p: int, n: int) -> int:
    for c in range(2, p):
        g = pow(c, (p - 1) // n, p)
        if pow(g, n // 2, p) == p - 1:
            return g
    raise RuntimeError("no element of order n")


def census_primes() -> list[int]:
    row = re.compile(r"^(\d+)\s+\d+\s+[0-9.]+\s+\S+\s+\d+\s+\d+\s+(\d+)\s+")
    primes = []
    for line in (HERE / "_out_466_d4_structure.txt").read_text().splitlines():
        match = row.match(line)
        if match:
            primes.append(int(match.group(1)))
    return primes


def dominant(triple: tuple[int, int, int]) -> bool:
    a = sorted(abs(t) for t in triple)
    return a[2] > a[0] + a[1]


def survey_prime(p: int, n: int, m: int, height: int, x) -> list[tuple]:
    """Return realized dominant trinomials (i, j, c0, c1, c2, res, quotient_or_None)."""
    g = element_of_order(p, n)
    assert pow(g, m, p) == p - 1
    roots = sorted({pow(g, j, p) for j in range(1, 2 * m, 2)})
    assert len(roots) == m
    powers = {z: [pow(z, e, p) for e in range(m)] for z in roots}
    nonzero = [c for c in range(-height, height + 1) if c != 0]
    found = []
    seen = set()
    for i, j in combinations(range(1, m), 2):
        for z in roots:
            zi, zj = powers[z][i], powers[z][j]
            for c1 in nonzero:
                base = (c1 * zi) % p
                for c2 in nonzero:
                    c0 = (-(base + c2 * zj)) % p
                    if not (1 <= c0 <= height):
                        continue
                    if not dominant((c0, c1, c2)):
                        continue
                    key = (i, j, c0, c1, c2)
                    if key in seen:
                        continue
                    seen.add(key)
                    res = abs(int(sp.resultant(x**m + 1, c0 + c1 * x**i + c2 * x**j, x)))
                    quot, rem = divmod(res, p)
                    dyadic = rem == 0 and quot > 0 and (quot & (quot - 1)) == 0
                    found.append((i, j, c0, c1, c2, res, quot if dyadic else None))
    return found


def main() -> int:
    x = sp.symbols("x")
    print("## dominant trinomial census, n=32, height<=8, all 92 K-bad primes")
    primes = census_primes()
    n, m, height = 32, 16, 8
    ok_small, ok_any, dead = [], [], []
    for p in primes:
        found = survey_prime(p, n, m, height, x)
        dyadics = [f for f in found if f[6] is not None]
        small = [f for f in dyadics if f[6] <= 8]
        if small:
            ok_small.append(p)
            best = min(small, key=lambda f: f[6])
            print(f"  p={p}: {len(found)} realized dominant, {len(dyadics)} dyadic, "
                  f"t<=3 witness {best[:5]} Res/p={best[6]}")
        elif dyadics:
            ok_any.append(p)
            best = min(dyadics, key=lambda f: f[6])
            print(f"  p={p}: {len(found)} realized dominant, best dyadic quotient "
                  f"{best[6]} (witness {best[:5]}) -- NO t<=3")
        else:
            dead.append(p)
            qs = sorted({f[5] // p if f[5] % p == 0 else None for f in found} - {None})
            print(f"  p={p}: {len(found)} realized dominant, ZERO dyadic quotients"
                  f" (p-divisible quotients seen: {qs[:6]})")
    print(f"SUMMARY n=32: {len(ok_small)}/92 have t<=3 dominant witness, "
          f"{len(ok_any)}/92 only larger dyadic, {len(dead)}/92 have NONE")
    if dead:
        print(f"  DEAD PRIMES (dominant repair fails): {dead}")

    print("## n=64 endpoint p=16778497 (r346 K-bad), height<=8 dominant trinomials")
    found64 = survey_prime(16778497, 64, 32, 8, x)
    dy64 = [f for f in found64 if f[6] is not None]
    print(f"  realized dominant trinomials: {len(found64)}; dyadic quotients: "
          f"{[(f[:5], f[6]) for f in dy64] if dy64 else 'NONE'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
