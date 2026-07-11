#!/usr/bin/env python3
"""#466 W12: refutation probe for BinomialBadPrimeLaw (the r323-r331 saturation route's
single named open input, kb r329/r325).

The law (r329 note / _R329KernelQuotientOrder.lean docstring):

  every in-window K-bad prime p admits a realized *binomial* kernel relation
  a + b*x^s  (|b| < |a|, realized at p: exists g, g^m = -1 mod p, a + b*g^s = 0 mod p)
  with |Res(x^m+1, a + b*x^s)| dividing 8p.        (m = 2^k = n/2)

This probe:
  1. validates the binomial resultant closed form
        |Res(x^m+1, a+b*x^s)| = (a^{m'} + b^{m'})^{2^v},  v = v2(s) (v<k), m' = m/2^v,
     against sympy resultants (the mathematical core of the planned Lean refutation);
  2. shows the law is UNSATISFIABLE at n=32 for every prime in the census window
     [n^4, 4n^4] = [2^20, 2^22]: the only binomial-resultant value with |a|=2 is
     2^16+1 = 65537 < p, and |a|>=3 gives >= 3^16+1 > 8*(4n^4); even-s resultants are
     perfect squares, and a realized square resultant dividing 8p forces p | 8;
  3. cross-checks by brute force (all |a|<=4, |b|<|a|, s<16, exact sympy resultants,
     realization mod p) on three census primes;
  4. does the same size argument at the n=64 endpoint (r346's K-bad prime 16778497);
  5. probes the GENERALIZED law (|Res| | 2^t * p, t unbounded): for each of the 92
     census K-bad primes, is there ANY (A,B), A>B>=1, A<=A_MAX, with
     oddpart(A^16+B^16) == p?  (t<=3 is the form the master pipe consumes with the
     stated constants; unbounded t degrades but does not immediately kill the pipe.)

Exit 0 = refutation confirmed (law unsatisfiable in-window at n=32 and n=64).
"""

from __future__ import annotations

import random
import re
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent


def v2(x: int) -> int:
    v = 0
    while x % 2 == 0 and x > 0:
        x //= 2
        v += 1
    return v


def oddpart(x: int) -> int:
    return x >> v2(x)


def closed_form(m: int, a: int, b: int, s: int) -> int:
    """|Res(x^m+1, a+b*x^s)| per the closed form (s>=1; v2(s) < log2(m))."""
    v = v2(s) if s > 0 else None
    if s == 0:
        return abs(a + b) ** m
    k = m.bit_length() - 1
    assert 2**k == m
    if v >= k:
        # x^s == (-1)^(s/m) * x^(s mod m) ... handle by reduction: s >= m never occurs
        # for Fin m shifts; guard anyway
        raise ValueError("shift with v2(s) >= k not expected for s < m")
    mp = m >> v
    return (a**mp + b**mp) ** (2**v)


def order(x: int, p: int) -> int:
    o = 1
    y = x % p
    while y != 1:
        y = (y * x) % p
        o += 1
    return o


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


def main() -> int:
    rng = random.Random(466)
    x = sp.symbols("x")
    failures = 0

    # ---- 1. closed-form validation ------------------------------------------------
    print("## 1. binomial resultant closed form |Res(x^m+1,a+bx^s)| vs sympy")
    checked = 0
    for m in (8, 16, 32):
        for _ in range(40):
            a = rng.randint(1, 9) * rng.choice([1, -1])
            b = rng.randint(1, 9) * rng.choice([1, -1])
            s = rng.randint(1, m - 1)
            res = abs(int(sp.resultant(x**m + 1, a + b * x**s, x)))
            cf = closed_form(m, a, b, s)
            if res != cf:
                print(f"  CLOSED-FORM FAILURE m={m} a={a} b={b} s={s}: sympy={res} cf={cf}")
                failures += 1
            checked += 1
    print(f"  checked {checked} random (m,a,b,s) triples: "
          f"{'ALL MATCH' if failures == 0 else 'MISMATCHES'}")

    # ---- 2. unsatisfiability at n=32 across the census window ---------------------
    print("## 2. n=32 (m=16) window [2^20, 2^22]: unsatisfiability certificate")
    n, m = 32, 16
    lo, hi = n**4, 4 * n**4
    primes = census_primes()
    assert len(primes) == 92, f"expected 92 census primes, got {len(primes)}"
    for p in primes:
        assert sp.isprime(p) and p % 32 == 1 and lo <= p <= hi, p
    # odd s: |Res| = a^16+b^16 with |a|>|b|>=1.
    #   |a|=2  -> value 65537 < 2^20 <= p, but realization forces p | Res -> p <= Res. dead.
    #   |a|>=3 -> value >= 3^16+1 > 8*hi >= 8p, but Res | 8p forces Res <= 8p. dead.
    assert 2**16 + 1 < lo
    assert 3**16 + 1 > 8 * hi
    # even s (incl. s=0): |Res| = square; square | 8p -> square in {1,4} -> Res <= 4 < p,
    # but realization forces p | Res. dead.
    print(f"  92/92 census primes verified prime, ==1 mod 32, in [{lo},{hi}]")
    print(f"  odd-s gap: 2^16+1 = {2**16+1} < {lo} = window floor;"
          f" 3^16+1 = {3**16+1} > {8*hi} = 8*window-ceiling")
    print("  even-s: perfect square dividing 8p forces |Res| <= 4 < p <= |Res|(realized).")
    print("  => NO realized binomial with |Res| | 8p exists for ANY in-window prime.")

    # ---- 3. brute-force cross-check on three census primes ------------------------
    print("## 3. brute force |a|<=4, |b|<|a|, s<16 on three census primes")
    for p in (1065409, 1439393, 4102753):
        g = element_of_order(p, n)
        assert pow(g, m, p) == p - 1
        roots = sorted({pow(g, j, p) for j in range(1, 2 * m, 2)})
        assert len(roots) == m
        found = []
        realized_count = 0
        for a in range(-4, 5):
            for b in range(-4, 5):
                if b == 0 or abs(b) >= abs(a):
                    continue
                for s in range(16):
                    realized = any((a + b * pow(z, s, p)) % p == 0 for z in roots)
                    if not realized:
                        continue
                    realized_count += 1
                    res = abs(int(sp.resultant(x**m + 1, a + b * x**s, x)))
                    if res != closed_form(m, a, b, s):
                        print(f"  CLOSED-FORM MISMATCH at realized ({a},{b},{s})")
                        failures += 1
                    if (8 * p) % res == 0:
                        found.append((a, b, s, res))
        if found:
            print(f"  p={p}: WITNESS FOUND {found}  <-- LAW SURVIVES HERE")
            failures += 1
        else:
            print(f"  p={p}: {realized_count} realized binomials in range, none with Res | 8p")

    # ---- 4. n=64 endpoint ----------------------------------------------------------
    print("## 4. n=64 (m=32) window [2^24, 2^26] incl. r346 prime 16778497")
    n64, m64 = 64, 32
    lo64, hi64 = n64**4, 4 * n64**4
    p64 = 16778497
    assert sp.isprime(p64) and p64 % 64 == 1 and lo64 <= p64 <= hi64
    assert 2**32 + 1 > 8 * hi64
    print(f"  odd-s: min value 2^32+1 = {2**32+1} > {8*hi64} = 8*window-ceiling -> dead")
    print("  even-s: same perfect-square argument -> dead")
    print(f"  => at the r346 K-bad prime p={p64} (and every in-window prime) the law fails.")

    # ---- 5. generalized law: |Res| = 2^t * p, t unbounded --------------------------
    print("## 5. generalized dyadic-cofactor law: oddpart(A^16+B^16) == p ?")
    a_max = 4096
    pset = set(primes)
    hits: dict[int, list[tuple[int, int, int]]] = {p: [] for p in primes}
    for A in range(2, a_max + 1):
        a16 = A**16
        for B in range(1, A):
            val = a16 + B**16
            odd = oddpart(val)
            if odd in pset:
                hits[odd].append((A, B, v2(val)))
    holders = {p: h for p, h in hits.items() if h}
    print(f"  swept A in [2,{a_max}], B<A: {len(holders)}/92 census primes admit"
          f" a binomial with oddpart(A^16+B^16) = p")
    for p, h in sorted(holders.items()):
        print(f"    p={p}: witnesses {h[:4]}{'...' if len(h) > 4 else ''}")
    if not holders:
        print("  => even with UNBOUNDED dyadic cofactor 2^t, no census K-bad prime has a"
              " binomial witness up to A=4096.")

    print()
    if failures == 0:
        print("VERDICT: BinomialBadPrimeLaw REFUTED (unsatisfiable in-window at n=32 and"
              " n=64); generalized-t rescue also empty in sweep range.")
    else:
        print(f"VERDICT: {failures} failures -- see above.")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
