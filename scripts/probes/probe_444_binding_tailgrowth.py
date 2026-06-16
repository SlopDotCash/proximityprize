#!/usr/bin/env python3
"""
probe_444_binding_tailgrowth.py  (#444, FRESH LENS [binding-restriction], part 3 - the union-bound test)

The union bound that yields sqrt(n log m) treats the m cosets as ~m near-independent
sub-Gaussian variables eta_b/sqrt(n).  The sqrt(log m) is the max-of-m scale.  The lens
hopes the EFFECTIVE number of independent directions is O(n), not m.

DIRECT TEST of "effective count":  Salem-Zygmund / max-of-m says
        E[max_b |eta_b|] ~ sqrt(n) * sqrt(2 log M_eff)
where M_eff is the effective number of independent cosets.  Invert:
        M_eff_hat = exp( (M_all / sqrt(n))^2 / 2 ).
If M_eff_hat tracks m (grows like m) => union bound is honest at scale m => sqrt(log m), lens fails.
If M_eff_hat saturates at ~n (independent of m) => effective directions = O(n), lens SURVIVES.

We scan, at FIXED n, a LADDER of primes with growing m, and watch whether
    M_all/sqrt(n)  grows like  sqrt(2 log m)   [m-driven, lens fails]
 or saturates near sqrt(2 log n) [n-driven, lens survives].

Also the honest budget check: at the prize log m=128, log n=30.  Even the BEST case
(M_eff = n) only helps if sqrt(log n)/sqrt(log m) = sqrt(30/128) = 0.484 pushes the
constant C from its plateau ~1.33 down below the Parseval/window floor.  Report the
implied constant under each hypothesis.
"""
import sympy, cmath, math
import numpy as np

TWO_PI = 2.0 * math.pi


def house(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = np.array([pow(h, j, p) for j in range(n)], dtype=np.int64)
    m = (p - 1) // n
    w = TWO_PI / p
    best = 0.0
    r = 1
    for _ in range(m):
        pr = (r * G) % p
        s = np.cos(w * pr).sum() + 1j * np.sin(w * pr).sum()
        a = abs(s)
        if a > best:
            best = a
        r = (r * g) % p
    return best, m


def ladder(n, count, pcap=2_000_000):
    out = []
    m = 2
    while len(out) < count:
        p = n * m + 1
        if p > pcap:
            break
        if sympy.isprime(p):
            out.append(p)
        m += 1
    return out


print("=" * 104)
print("LENS [binding-restriction] part 3: does the house track sqrt(2 log m) [m-driven] or saturate [n-driven]?")
print("=" * 104)
print(f"{'n':>4} {'p':>9} {'m':>7} {'M/sqrtn':>8} {'sqrt(2lnM)':>10} {'sqrt(2lnN)':>10} "
      f"{'Meff_hat':>10} {'Meff/m':>8} {'Meff/n':>8}")
print("-" * 104)

for n in (16, 32, 64, 128):
    s2lnN = math.sqrt(2 * math.log(n))
    for p in ladder(n, 10):
        M, m = house(n, p)
        Msn = M / math.sqrt(n)
        s2lnM = math.sqrt(2 * math.log(m)) if m > 1 else float('nan')
        Meff = math.exp(Msn * Msn / 2.0)
        print(f"{n:>4} {p:>9} {m:>7} {Msn:>8.3f} {s2lnM:>10.3f} {s2lnN:>10.3f} "
              f"{Meff:>10.1f} {Meff/m:>8.3f} {Meff/n:>8.3f}")
    print("-" * 104)

print()
print("READOUT:")
print("  Meff/m ~ const (and Meff >> n)  => effective directions scale with m => sqrt(log m) honest => LENS FAILS")
print("  Meff/n ~ const (Meff saturates) => effective directions = O(n)        => sqrt(log n) => LENS SURVIVES")
print()
print("Budget at prize (log m=128, log n=30):  C_logm = 1.33  =>  C_logn = 1.33*sqrt(128/30) =",
      round(1.33 * math.sqrt(128 / 30), 3), "(if lens held, the bound would WORSEN unless re-derived)")
