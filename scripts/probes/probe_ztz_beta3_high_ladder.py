#!/usr/bin/env python3
"""Sieve two-factor-Lucas certifiable primes for the cubic (beta=3) TZ ladder,
high rungs n in {8192, 16384} = 2^{13,14}.

For each target modulus n:
  * window [n^3, 2*n^3]  (n=8192 -> [2^39, 2^40]; n=16384 -> [2^42, 2^43])
  * find primes p == 1 (mod n) inside the window with p-1 = 2^e * c, c an odd prime
    (the two-factor Lucas shape consumed by `lucasTwoFactor` in the Lean file)
  * pick a Lucas witness g (try g=3 first; require g^(p-1)=1, g^((p-1)/2)!=1,
    g^((p-1)/c)!=1 mod p) and only keep primes where g=3 works, for a uniform cert.

Primality is exact: deterministic Miller-Rabin with the witness set
[2,3,5,7,11,13,17,19,23,29,31,37], which is proven correct for all n < 3.3e24;
our candidates are < 2^44 ~ 1.8e13, comfortably inside that bound.

Output is paste-ready Lean certificate lines for
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ZTZBetaThreeHighLadderExtension.lean
"""

# Deterministic Miller-Rabin witnesses (exact below 3.3e24).
_MR_WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_WITNESSES:
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
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def two_factor_shape(p: int):
    """Return (e, c) with p-1 = 2^e * c, c odd, and c an odd prime; else None."""
    m = p - 1
    e = 0
    while m % 2 == 0:
        m //= 2
        e += 1
    if m > 1 and is_prime(m):
        return e, m
    return None


def lucas_witness_ok(g: int, p: int, e: int, c: int) -> bool:
    """Check g certifies p via the two-factor Lucas test."""
    if pow(g, p - 1, p) != 1:
        return False
    if pow(g, (p - 1) // 2, p) == 1:
        return False
    if pow(g, (p - 1) // c, p) == 1:
        return False
    return True


def find_rung(n: int, count: int, g: int = 3):
    lo = n ** 3           # ceil(n^3) since n^3 is an integer
    hi = 2 * (n ** 3)     # floor(2 n^3)
    # first candidate >= lo with p == 1 (mod n)
    start = lo + ((1 - lo) % n)
    if start < lo:
        start += n
    p = start
    found = []
    scanned = 0
    while p <= hi and len(found) < count:
        scanned += 1
        if is_prime(p):
            shape = two_factor_shape(p)
            if shape is not None:
                e, c = shape
                if lucas_witness_ok(g, p, e, c):
                    found.append((p, e, c))
        p += n
    return found, scanned, lo, hi


def emit(n: int, found, lo, hi):
    print(f"# ---- n = {n} = 2^{n.bit_length()-1}, window [{lo}, {hi}] = "
          f"[2^{lo.bit_length()-1}, 2^{hi.bit_length()-1}] ----")
    print(f"# found {len(found)} primes p == 1 (mod {n}) with p-1 = 2^e * c, g=3")
    for (p, e, c) in found:
        assert p - 1 == 2 ** e * c, (p, e, c)
        assert is_prime(p) and is_prime(c)
        assert lo <= p <= hi and p % n == 1
        print(f"private theorem prime_{p} : Nat.Prime {p} :=")
        print(f"  lucasTwoFactor {c} {e} 3 (by norm_num) (by norm_num)")
        print("    (by rw [← binaryPow_eq_pow]; decide)")
        print("    (by rw [← binaryPow_eq_pow]; decide)")
        print("    (by rw [← binaryPow_eq_pow]; decide)")
    print("# Finset (paste-ready):")
    print("#   " + ", ".join(str(p) for (p, _, _) in found))
    print()


def main():
    for n, name in ((8192, "8192"), (16384, "16384")):
        found, scanned, lo, hi = find_rung(n, 12)
        if len(found) < 12:
            print(f"# WARNING: only found {len(found)} for n={n} after scanning {scanned}")
        emit(n, found, lo, hi)


if __name__ == "__main__":
    main()
