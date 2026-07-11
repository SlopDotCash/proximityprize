#!/usr/bin/env python3
"""
probe_ztz_beta3_ladder.py  (#466, lane res:tz-prize-scale, beta=3 ladder extension)

Find explicit two-factor Lucas certificate data for primes p in the Thorner-Zaman
window [n^3, 2*n^3] with p ≡ 1 (mod n), for n = 2^k beyond the current concrete
ladder maximum (n = 256).  These feed the axiom-clean Lean theorems
`tzPrimeSupply_{512,1024,2048,4096}_three` in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ZTZBetaThreeLadderExtension.lean`.

For each target n = 2^k it prints, per selected window prime p:
    p = 2^a * c + 1,   c an odd prime,   g a Lucas witness
in ready-to-paste Lean form:
    lucasTwoFactor <c> <a> <g> (by norm_num) (by norm_num)
      (by rw [← binaryPow_eq_pow]; decide)
      (by rw [← binaryPow_eq_pow]; decide)
      (by rw [← binaryPow_eq_pow]; decide)

Determinism: Miller-Rabin with the fixed witness set proven correct for all
n < 3.3 * 10^24 (Sorenson-Webster), so all primality decisions below ~2^80 are exact.
"""

import sys

# Deterministic Miller-Rabin: this witness set is correct for all n < 3.317e24.
_MR_WITNESSES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in _MR_WITNESSES:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def two_factor(pm1: int):
    """Factor pm1 = 2^a * c with c odd.  Return (a, c)."""
    a = 0
    c = pm1
    while c % 2 == 0:
        c //= 2
        a += 1
    return a, c


def lucas_witness(p: int, a: int, c: int):
    """Smallest small g in {2,3,5,7,11,...} with g^(p-1)=1, g^((p-1)/2)!=1,
    g^((p-1)/c)!=1 mod p.  Returns g or None."""
    pm1 = p - 1
    for g in (3, 2, 5, 7, 11, 13, 17, 19):
        if g % p == 0:
            continue
        if pow(g, pm1, p) != 1:
            continue
        if pow(g, pm1 // 2, p) == 1:
            continue
        if pow(g, pm1 // c, p) == 1:
            continue
        return g
    return None


def find_certs(k: int, count: int):
    """For n = 2^k, β = 3, find up to `count` window primes with clean
    two-factor Lucas certs.  Prefer witness g = 3 for uniformity."""
    n = 1 << k
    lo = n ** 3
    hi = 2 * (n ** 3)
    results = []
    # walk p = 1 + n*t upward from just inside the lower boundary
    t0 = (lo - 1) // n + 1
    t = t0
    while len(results) < count:
        p = 1 + n * t
        if p > hi:
            break
        t += 1
        if not is_prime(p):
            continue
        a, c = two_factor(p - 1)
        if not is_prime(c):
            continue  # need the odd cofactor prime for a TWO-factor cert
        if c == 1:
            continue
        g = lucas_witness(p, a, c)
        if g is None:
            continue
        results.append((p, a, c, g))
    return n, lo, hi, results


def emit(k: int, count: int):
    n, lo, hi, results = find_certs(k, count)
    print(f"# ===== n = 2^{k} = {n},  beta = 3 =====")
    print(f"#   window [n^3, 2 n^3] = [{lo}, {hi}]")
    print(f"#   found {len(results)} certifiable window primes (p ≡ 1 mod {n})")
    all_g3 = all(g == 3 for (_, _, _, g) in results)
    print(f"#   all witnesses g = 3 ? {all_g3}")
    print(f"#   n^3 = {lo}")
    for (p, a, c, g) in results:
        assert 1 + (1 << a) * c == p
        assert lo <= p <= hi
        assert p % n == 1
        assert is_prime(p) and is_prime(c)
        print(f"prime_{p}:  p-1 = 2^{a} * {c},  g = {g}")
        print(f"  lucasTwoFactor {c} {a} {g} (by norm_num) (by norm_num)")
    # emit the Lean Finset literal for the card proof
    plist = [str(p) for (p, _, _, _) in results]
    print("#   Finset literal:")
    print("#   {" + ", ".join(plist) + "}")
    print()
    return n, lo, results


if __name__ == "__main__":
    # default: n = 512, 1024, 2048, 4096; 12 primes each
    targets = [(9, 12), (10, 12), (11, 12), (12, 12)]
    if len(sys.argv) > 1:
        targets = [(int(sys.argv[i]), 12) for i in range(1, len(sys.argv))]
    for (k, count) in targets:
        emit(k, count)
